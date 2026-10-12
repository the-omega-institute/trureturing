/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite-evaluator simulation of original partial effective selectors in native serial operations. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeSerialMachine

/-! ### The original selector interface

The separate packet machine is deliberately small; the source semantics of
an original selector keeps the source selector's
common input, workspace, certified epoch, and complete chronological acquired
record in its state.  Its selector is a partial recursive function: a source
may spend arbitrarily many finite local steps before producing its next
external action, and may diverge on states which no allowed source reaches.
The finite evaluator below is only an implementation of this partial
function; it is not a total next-boundary oracle.
-/

/-- An acquired external event, retaining every update epoch and every
physical read/reply pair.  Local evaluator work is not a source-visible event. -/
abbrev OriginalEvent := Sum Nat (Nat × Address × Nat)

/-- Common input, accessible workspace, current certified epoch, and the full
chronological acquired record. -/
abbrev OriginalState := Nat × Nat × Nat × List OriginalEvent

def OriginalState.input (s : OriginalState) : Nat := s.1
def OriginalState.epoch (s : OriginalState) : Nat := s.2.2.1
def OriginalState.history (s : OriginalState) : List OriginalEvent := s.2.2.2

def originalReplyCode : Reply → Nat
  | .alpha => 0
  | .beta => 1
  | .branch => 2
  | .absent => 3

def afterOriginalRead (s : OriginalState) (a : Address) (y : Reply)
    (workspace : Nat) : OriginalState :=
  (s.input, workspace, s.epoch,
    s.history ++ [.inr (s.epoch, a, originalReplyCode y)])

def afterOriginalUpdate (s : OriginalState) (workspace : Nat) : OriginalState :=
  (s.input, workspace, s.epoch + 1,
    s.history ++ [.inl s.epoch])

/-- The source action language is independent of `Packet`: continuations are
workspace values and the source transition relation appends the actual event
and advances the certified epoch itself.  Local selector work is represented by
the partial computation of `select`, not by a source-visible event. -/
abbrev OriginalAction (O : Type) :=
  (Address × (Nat × Nat × Nat × Nat)) ⊕ (Nat ⊕ O)

def originalRead {O : Type} (a : Address)
    (continuations : Nat × Nat × Nat × Nat) : OriginalAction O :=
  .inl (a, continuations)

def originalUpdate {O : Type} (workspace : Nat) : OriginalAction O :=
  .inr (.inl workspace)

def originalStop {O : Type} (output : O) : OriginalAction O :=
  .inr (.inr output)

def originalContinuation (k : Nat × Nat × Nat × Nat) (y : Reply) : Nat :=
  match y with
  | .alpha => k.1
  | .beta => k.2.1
  | .branch => k.2.2.1
  | .absent => k.2.2.2

structure OriginalEffectiveService (O : Type) [Primcodable O] where
  /-- The source selector may be partial away from its reached states. -/
  select : OriginalState → Part (OriginalAction O)
  effective : Partrec select

/-! The source-level run relation.  Its read premises use the actual current
register, while its state records the same event and continuation that the
native machine will later expose. -/

inductive OriginalRun {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) :
    OriginalState → Source → Trace → O → Prop
  | stop {s r o} :
      originalStop o ∈ S.select s →
      OriginalRun S s r [] o
  | update {s r t o workspace} :
      originalUpdate workspace ∈ S.select s →
      OriginalRun S (afterOriginalUpdate s workspace)
        (substitution r) t o →
      OriginalRun S s r (.update s.epoch :: t) o
  | read {s r t o a k y} :
      originalRead a k ∈ S.select s →
      readout a r = y →
      OriginalRun S (afterOriginalRead s a y (originalContinuation k y))
        r t o →
      OriginalRun S s r (.read s.epoch a y :: t) o

/-! ### Code realization and bounded evaluator

`Partrec` is first converted to the exact pinned `Nat.Partrec.Code` supplied by
mathlib.  The code is evaluated only with `evaln`; `evaln_complete` supplies a
finite fuel witness on each actually reached selector state, while no value is
claimed on a diverging unreachable state.
-/

noncomputable def originalSelectorCode {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp S.effective)

private theorem originalSelectorCode_spec {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) :
    Nat.Partrec.Code.eval (originalSelectorCode S) =
    (fun n => Part.bind (Part.ofOption (Encodable.decode n))
        (fun s => (S.select s).map Encodable.encode)) := by
  exact Classical.choose_spec (Nat.Partrec.Code.exists_code.mp S.effective)

noncomputable def evalOriginalAction {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) (fuel stateCode : Nat) :
    Option (OriginalAction O) :=
  (Nat.Partrec.Code.evaln fuel (originalSelectorCode S) stateCode).bind
    (fun n => Encodable.decode n)

private theorem evalOriginalAction_effective {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) : Computable₂ (evalOriginalAction S) := by
  apply Computable.option_bind
    (Nat.Partrec.Code.primrec_evaln.to_comp.comp
      ((Computable.fst.pair (Computable.const (originalSelectorCode S))).pair Computable.snd))
  exact (Computable.decode.comp Computable.snd).to₂

private theorem evalOriginalAction_complete {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) (s : OriginalState)
    {a : OriginalAction O} (ha : a ∈ S.select s) :
    ∃ fuel, evalOriginalAction S fuel (Encodable.encode s) = some a := by
  have hs : Encodable.encode a ∈
      Nat.Partrec.Code.eval (originalSelectorCode S) (Encodable.encode s) := by
    rw [originalSelectorCode_spec]
    simpa using ha
  obtain ⟨fuel,hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hs
  refine ⟨fuel, ?_⟩
  change (Nat.Partrec.Code.evaln fuel (originalSelectorCode S) (Encodable.encode s)).bind
      (fun n => Encodable.decode n) = some a
  rw [show Nat.Partrec.Code.evaln fuel (originalSelectorCode S) (Encodable.encode s) =
      some (Encodable.encode a) by simpa using hfuel]
  change @Encodable.decode (OriginalAction O) _ (Encodable.encode a) = some a
  exact Encodable.encodek a

private theorem evalOriginalAction_sound {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) (s : OriginalState) {fuel : Nat}
    {a : OriginalAction O}
    (h : evalOriginalAction S fuel (Encodable.encode s) = some a) :
    a ∈ S.select s := by
  cases he : Nat.Partrec.Code.evaln fuel (originalSelectorCode S) (Encodable.encode s) with
  | none => simp [evalOriginalAction, he] at h
  | some n =>
      have hdecode : Encodable.decode n = some a := by
        simpa [evalOriginalAction, he] using h
      have hn : n ∈
          Nat.Partrec.Code.evaln fuel (originalSelectorCode S) (Encodable.encode s) := by
        simp [he]
      have hs := Nat.Partrec.Code.evaln_sound hn
      rw [originalSelectorCode_spec] at hs
      rcases Part.mem_bind_iff.mp hs with ⟨s', hs', ha'⟩
      rcases (Part.mem_map_iff Encodable.encode).mp ha' with ⟨a', haS, hencode⟩
      have hstate : s' = s := by simpa using hs'
      have haction : a' = a := by
        have hd := congrArg
          (fun z : Nat => @Encodable.decode (OriginalAction O) _ z) hencode
        simpa [hdecode] using hd
      simpa [hstate, haction] using haS

private theorem evalOriginalAction_none_before {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) (s : OriginalState)
    (a : OriginalAction O) {m : Nat}
    (ha : a ∈ S.select s)
    (minimal : ∀ k, k < m →
      evalOriginalAction S k (Encodable.encode s) ≠ some a) :
    ∀ k < m, evalOriginalAction S k (Encodable.encode s) = none := by
  intro k hk
  cases h : evalOriginalAction S k (Encodable.encode s) with
  | none => rfl
  | some act =>
      have hs := evalOriginalAction_sound S s h
      have heq : act = a := Part.mem_unique hs ha
      have hp_k : evalOriginalAction S k (Encodable.encode s) = some a := by
        simpa [heq] using h
      exfalso
      exact (minimal k hk) hp_k

def originalControl (s : OriginalState) (fuel : Nat) : Nat :=
  Nat.pair (Encodable.encode s) fuel

noncomputable def originalNativeControl {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) (control : Nat) : Op Nat O := by
  classical
  exact match Encodable.decode control.unpair.1 with
  | none => .localStep (Nat.pair control.unpair.1 (control.unpair.2 + 1))
  | some s =>
      match evalOriginalAction S control.unpair.2 control.unpair.1 with
      | none => .localStep (Nat.pair control.unpair.1 (control.unpair.2 + 1))
      | some (.inl (a,k)) =>
          .read a (fun y =>
            originalControl (afterOriginalRead s a y (originalContinuation k y)) 0)
      | some (.inr (.inl workspace)) =>
          .applyRho (originalControl (afterOriginalUpdate s workspace) 0)
      | some (.inr (.inr o)) => .stop o

/-! ### Explicit executable code backend

The extensional service above remains the public arbitrary-service interface.
For execution, a caller supplies the actual `Nat.Partrec.Code` together with
its realization equation.  The code is data, so the bounded evaluator and
controller below reduce in Lean's runtime; the realization proof is used only
to connect their traces back to the same original selector. -/

structure OriginalCodeRealization {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) where
  code : Nat.Partrec.Code
  realizes : ∀ s : OriginalState,
    Nat.Partrec.Code.eval code (Encodable.encode s) =
      (S.select s).map Encodable.encode

noncomputable def originalCodeRealization {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) : OriginalCodeRealization S :=
  ⟨originalSelectorCode S, fun s => by
    rw [originalSelectorCode_spec]
    simp⟩

def evalOriginalActionFromCode {O : Type} [Primcodable O]
    (code : Nat.Partrec.Code) (stage stateCode : Nat) : Option (OriginalAction O) :=
  (Nat.Partrec.Code.evaln (2^stage) code stateCode).bind
    (fun n => Encodable.decode n)

def evalOriginalActionCode {O : Type} [Primcodable O]
    {S : OriginalEffectiveService O} (R : OriginalCodeRealization S)
    (fuel stateCode : Nat) : Option (OriginalAction O) :=
  evalOriginalActionFromCode R.code fuel stateCode

theorem evalOriginalActionCode_sound {O : Type} [Primcodable O]
    {S : OriginalEffectiveService O} (R : OriginalCodeRealization S)
    (s : OriginalState) {fuel : Nat} {a : OriginalAction O}
    (h : evalOriginalActionCode R fuel (Encodable.encode s) = some a) :
    a ∈ S.select s := by
  cases he : Nat.Partrec.Code.evaln (2^fuel) R.code (Encodable.encode s) with
  | none => simp [evalOriginalActionCode, evalOriginalActionFromCode, he] at h
  | some n =>
      have hdecode : Encodable.decode n = some a := by
        simpa [evalOriginalActionCode, evalOriginalActionFromCode, he] using h
      have hn : n ∈ Nat.Partrec.Code.evaln (2^fuel) R.code (Encodable.encode s) := by
        simp [he]
      have hs := Nat.Partrec.Code.evaln_sound hn
      rw [R.realizes s] at hs
      rcases (Part.mem_map_iff Encodable.encode).mp hs with ⟨a', haS, hencode⟩
      have haction : a' = a := by
        have hd := congrArg
          (fun z : Nat => @Encodable.decode (OriginalAction O) _ z) hencode
        simpa [hdecode] using hd
      simpa [haction] using haS

theorem evalOriginalActionCode_complete {O : Type} [Primcodable O]
    {S : OriginalEffectiveService O} (R : OriginalCodeRealization S)
    (s : OriginalState) {a : OriginalAction O} (ha : a ∈ S.select s) :
    ∃ fuel, evalOriginalActionCode R fuel (Encodable.encode s) = some a := by
  have hs : Encodable.encode a ∈ Nat.Partrec.Code.eval R.code (Encodable.encode s) := by
    rw [R.realizes s]
    simpa using ha
  obtain ⟨fuel,hfuel0⟩ := Nat.Partrec.Code.evaln_complete.mp hs
  have hfuel := Nat.Partrec.Code.evaln_mono
    (show fuel ≤ 2^fuel from Nat.le_of_lt (Nat.lt_two_pow_self)) hfuel0
  refine ⟨fuel, ?_⟩
  change (Nat.Partrec.Code.evaln (2^fuel) R.code (Encodable.encode s)).bind
      (fun n => Encodable.decode n) = some a
  rw [show Nat.Partrec.Code.evaln (2^fuel) R.code (Encodable.encode s) =
      some (Encodable.encode a) by simpa using hfuel]
  change @Encodable.decode (OriginalAction O) _ (Encodable.encode a) = some a
  exact Encodable.encodek a

private theorem evalOriginalActionCode_none_before {O : Type} [Primcodable O]
    {S : OriginalEffectiveService O} (R : OriginalCodeRealization S) (s : OriginalState)
    (a : OriginalAction O) {m : Nat} (ha : a ∈ S.select s)
    (minimal : ∀ k, k < m →
      evalOriginalActionCode R k (Encodable.encode s) ≠ some a) :
    ∀ k < m, evalOriginalActionCode R k (Encodable.encode s) = none := by
  intro k hk
  cases h : evalOriginalActionCode R k (Encodable.encode s) with
  | none => rfl
  | some act =>
      have hs := evalOriginalActionCode_sound R s h
      have heq : act = a := Part.mem_unique hs ha
      have hp_k : evalOriginalActionCode R k (Encodable.encode s) = some a := by
        simpa [heq] using h
      exfalso
      exact (minimal k hk) hp_k

def originalNativeControlFromCode {O : Type} [Primcodable O]
    (code : Nat.Partrec.Code) (control : Nat) : Op Nat O :=
  match Encodable.decode control.unpair.1 with
  | none => .localStep (Nat.pair control.unpair.1 (control.unpair.2 + 1))
  | some s =>
      match evalOriginalActionFromCode code control.unpair.2 control.unpair.1 with
      | none => .localStep (Nat.pair control.unpair.1 (control.unpair.2 + 1))
      | some (.inl (a,k)) =>
          .read a (fun y =>
            originalControl (afterOriginalRead s a y (originalContinuation k y)) 0)
      | some (.inr (.inl workspace)) =>
          .applyRho (originalControl (afterOriginalUpdate s workspace) 0)
      | some (.inr (.inr o)) => .stop o

def originalNativeControlCode {O : Type} [Primcodable O]
    {S : OriginalEffectiveService O} (R : OriginalCodeRealization S) (control : Nat) : Op Nat O :=
  originalNativeControlFromCode R.code control

def eraseEvaluatorSteps : Trace → Trace
  | [] => []
  | .localStep :: t => eraseEvaluatorSteps t
  | e :: t => e :: eraseEvaluatorSteps t

@[simp] private theorem eraseEvaluatorSteps_replicate (m : Nat) (t : Trace) :
    eraseEvaluatorSteps (List.replicate m .localStep ++ t) = eraseEvaluatorSteps t := by
  induction m with
  | zero => rfl
  | succ m ih => simpa [List.replicate_succ, eraseEvaluatorSteps] using ih

set_option maxHeartbeats 1000000 in
-- The explicit-code backend has the same finite fuel-prefix induction.
private theorem original_native_prefix {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) (s : OriginalState) (r : Source)
    {f : Nat} {tail : Trace} {o : O}
    (terminal : Run (originalNativeControl S) (originalControl s f) s.epoch r tail o)
    (none_before : ∀ k, k < f →
      evalOriginalAction S k (Encodable.encode s) = none) :
    Run (originalNativeControl S) (originalControl s 0) s.epoch r
      (List.replicate f .localStep ++ tail) o := by
  have aux : ∀ (start m : Nat), start + m = f →
      (∀ k, start ≤ k → k < start + m →
        evalOriginalAction S k (Encodable.encode s) = none) →
      Run (originalNativeControl S) (originalControl s start) s.epoch r
        (List.replicate m .localStep ++ tail) o := by
    intro start m
    induction m generalizing start with
    | zero =>
        intro hsum _
        have hstart : start = f := by omega
        subst start
        exact terminal
    | succ m ih =>
        intro hsum hnone
        have hstart : evalOriginalAction S start (Encodable.encode s) = none :=
          hnone start le_rfl (by omega)
        have hstep : originalNativeControl S (originalControl s start) =
            .localStep (originalControl s (start + 1)) := by
          simp only [originalNativeControl, originalControl, Nat.unpair_pair]
          rw [Encodable.encodek, hstart]
        apply Run.localStep hstep
        apply ih (start := start + 1) (by omega)
        intro k hk₁ hk₂
        exact hnone k (by omega) (by omega)
  apply aux 0 f (by simp)
  intro k hk₁ hk₂
  exact none_before k (by simpa using hk₂)

set_option maxHeartbeats 2000000 in
-- Each boundary case realizes and concatenates its finite evaluator prefix.
private theorem original_run_to_native {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) {s : OriginalState} {r : Source}
    {t : Trace} {o : O} (run : OriginalRun S s r t o) :
    ∃ nt, Run (originalNativeControl S) (originalControl s 0) s.epoch r nt o ∧
      eraseEvaluatorSteps nt = t := by
  classical
  induction run with
  | @stop s r o ha =>
      obtain ⟨f,hf⟩ := evalOriginalAction_complete S s ha
      let p : Nat → Prop := fun k =>
        evalOriginalAction S k (Encodable.encode s) = some (originalStop o)
      have hp : ∃ k, p k := ⟨f,hf⟩
      let m := Nat.find hp
      have hm : p m := Nat.find_spec hp
      dsimp [p] at hm
      have hnone : ∀ k, k < m →
          evalOriginalAction S k (Encodable.encode s) = none := by
        apply evalOriginalAction_none_before S s (originalStop o) ha
        intro k hk hEq
        exact Nat.not_lt_of_ge (Nat.find_min' hp (by simpa [p] using hEq)) hk
      have hterminal : Run (originalNativeControl S) (originalControl s m)
          s.epoch r [] o := by
        have hstop : originalNativeControl S (originalControl s m) =
            .stop o := by
          simp only [originalNativeControl, originalControl, Nat.unpair_pair]
          rw [Encodable.encodek, hm]
          rfl
        exact Run.stop (by simpa [hstop])
      refine ⟨List.replicate m .localStep, ?_, ?_⟩
      · simpa using (original_native_prefix S s r hterminal hnone)
      · induction m with
        | zero => rfl
        | succ m ih => simpa [List.replicate_succ, eraseEvaluatorSteps] using ih
  | @update s r t o workspace ha runTail ih =>
      obtain ⟨f,hf⟩ := evalOriginalAction_complete S s ha
      let p : Nat → Prop := fun k =>
        evalOriginalAction S k (Encodable.encode s) = some (originalUpdate workspace)
      have hp : ∃ k, p k := ⟨f,hf⟩
      let m := Nat.find hp
      have hm : p m := Nat.find_spec hp
      dsimp [p] at hm
      have hnone : ∀ k, k < m →
          evalOriginalAction S k (Encodable.encode s) = none := by
        apply evalOriginalAction_none_before S s (originalUpdate workspace) ha
        intro k hk hEq
        exact Nat.not_lt_of_ge (Nat.find_min' hp (by simpa [p] using hEq)) hk
      obtain ⟨nt,tail,he⟩ := ih
      have hterminal : Run (originalNativeControl S) (originalControl s m)
          s.epoch r (.update s.epoch :: nt) o := by
        have hup : originalNativeControl S (originalControl s m) =
            .applyRho (originalControl (afterOriginalUpdate s workspace) 0) := by
          simp only [originalNativeControl, originalControl, Nat.unpair_pair]
          rw [Encodable.encodek, hm]
          rfl
        apply Run.update hup
        simpa [afterOriginalUpdate, OriginalState.epoch] using tail
      refine ⟨List.replicate m .localStep ++ (.update s.epoch :: nt), ?_, ?_⟩
      · exact original_native_prefix S s r hterminal hnone
      · simp [eraseEvaluatorSteps, he]
  | @read s r t o a cont y ha hy runTail ih =>
      obtain ⟨f,hf⟩ := evalOriginalAction_complete S s ha
      let p : Nat → Prop := fun j =>
        evalOriginalAction S j (Encodable.encode s) = some (originalRead a cont)
      have hp : ∃ k, p k := ⟨f,hf⟩
      let m := Nat.find hp
      have hm : p m := Nat.find_spec hp
      dsimp [p] at hm
      have hnone : ∀ k, k < m →
          evalOriginalAction S k (Encodable.encode s) = none := by
        apply evalOriginalAction_none_before S s (originalRead a cont) ha
        intro j hj hEq
        exact Nat.not_lt_of_ge (Nat.find_min' hp (by simpa [p] using hEq)) hj
      obtain ⟨nt,tail,he⟩ := ih
      have hterminal : Run (originalNativeControl S) (originalControl s m)
          s.epoch r (.read s.epoch a y :: nt) o := by
        have hr : originalNativeControl S (originalControl s m) =
            .read a (fun z =>
              originalControl (afterOriginalRead s a z (originalContinuation cont z)) 0) := by
          simp only [originalNativeControl, originalControl, Nat.unpair_pair]
          rw [Encodable.encodek, hm]
          rfl
        apply Run.read hr hy
        simpa [afterOriginalRead, OriginalState.epoch] using tail
      refine ⟨List.replicate m .localStep ++ (.read s.epoch a y :: nt), ?_, ?_⟩
      · exact original_native_prefix S s r hterminal hnone
      · simp [eraseEvaluatorSteps, he]


set_option maxHeartbeats 1000000 in
-- The explicit-code backend has the same finite fuel-prefix induction.
private theorem original_code_native_prefix {O : Type} [Primcodable O]
    {S : OriginalEffectiveService O} (R : OriginalCodeRealization S) (s : OriginalState) (r : Source)
    {f : Nat} {tail : Trace} {o : O}
    (terminal : Run (originalNativeControlCode R) (originalControl s f) s.epoch r tail o)
    (none_before : ∀ k, k < f →
      evalOriginalActionCode R k (Encodable.encode s) = none) :
    Run (originalNativeControlCode R) (originalControl s 0) s.epoch r
      (List.replicate f .localStep ++ tail) o := by
  have aux : ∀ (start m : Nat), start + m = f →
      (∀ k, start ≤ k → k < start + m →
        evalOriginalActionCode R k (Encodable.encode s) = none) →
      Run (originalNativeControlCode R) (originalControl s start) s.epoch r
        (List.replicate m .localStep ++ tail) o := by
    intro start m
    induction m generalizing start with
    | zero =>
        intro hsum _
        have hstart : start = f := by omega
        subst start
        exact terminal
    | succ m ih =>
        intro hsum hnone
        have hstart : evalOriginalActionCode R start (Encodable.encode s) = none :=
          hnone start le_rfl (by omega)
        have hstep : originalNativeControlCode R (originalControl s start) =
            .localStep (originalControl s (start + 1)) := by
          have hstart' :
              (Nat.Partrec.Code.evaln (2^start) R.code (Encodable.encode s)).bind
                  (fun n => @Encodable.decode (OriginalAction O) _ n) = none := by
            simpa [evalOriginalActionCode, evalOriginalActionFromCode] using hstart
          simp only [originalNativeControlCode, originalNativeControlFromCode,
            evalOriginalActionCode, evalOriginalActionFromCode, originalControl,
            Nat.unpair_pair]
          rw [Encodable.encodek, hstart']
        apply Run.localStep hstep
        apply ih (start := start + 1) (by omega)
        intro k hk₁ hk₂
        exact hnone k (by omega) (by omega)
  apply aux 0 f (by simp)
  intro k hk₁ hk₂
  exact none_before k (by simpa using hk₂)

set_option maxHeartbeats 2000000 in
-- Each explicit-code boundary case realizes and concatenates its finite prefix.
private theorem original_code_run_to_native {O : Type} [Primcodable O]
    {S : OriginalEffectiveService O} (R : OriginalCodeRealization S) {s : OriginalState} {r : Source}
    {t : Trace} {o : O} (run : OriginalRun S s r t o) :
    ∃ nt, Run (originalNativeControlCode R) (originalControl s 0) s.epoch r nt o ∧
      eraseEvaluatorSteps nt = t := by
  classical
  induction run with
  | @stop s r o ha =>
      obtain ⟨f,hf⟩ := evalOriginalActionCode_complete R s ha
      let p : Nat → Prop := fun k =>
        evalOriginalActionCode R k (Encodable.encode s) = some (originalStop o)
      have hp : ∃ k, p k := ⟨f,hf⟩
      let m := Nat.find hp
      have hm : p m := Nat.find_spec hp
      dsimp [p] at hm
      have hnone : ∀ k, k < m →
          evalOriginalActionCode R k (Encodable.encode s) = none := by
        apply evalOriginalActionCode_none_before R s (originalStop o) ha
        intro k hk hEq
        exact Nat.not_lt_of_ge (Nat.find_min' hp (by simpa [p] using hEq)) hk
      have hterminal : Run (originalNativeControlCode R) (originalControl s m)
          s.epoch r [] o := by
        have hstop : originalNativeControlCode R (originalControl s m) =
            .stop o := by
          have hm' :
              (Nat.Partrec.Code.evaln (2^m) R.code (Encodable.encode s)).bind
                  (fun n => @Encodable.decode (OriginalAction O) _ n) = some (originalStop o) := by
            simpa [evalOriginalActionCode, evalOriginalActionFromCode] using hm
          simp only [originalNativeControlCode, originalNativeControlFromCode,
            evalOriginalActionCode, evalOriginalActionFromCode, originalControl,
            Nat.unpair_pair]
          rw [Encodable.encodek, hm']
          rfl
        exact Run.stop (by simpa [hstop])
      refine ⟨List.replicate m .localStep, ?_, ?_⟩
      · simpa using (original_code_native_prefix R s r hterminal hnone)
      · induction m with
        | zero => rfl
        | succ m ih => simpa [List.replicate_succ, eraseEvaluatorSteps] using ih
  | @update s r t o workspace ha runTail ih =>
      obtain ⟨f,hf⟩ := evalOriginalActionCode_complete R s ha
      let p : Nat → Prop := fun k =>
        evalOriginalActionCode R k (Encodable.encode s) = some (originalUpdate workspace)
      have hp : ∃ k, p k := ⟨f,hf⟩
      let m := Nat.find hp
      have hm : p m := Nat.find_spec hp
      dsimp [p] at hm
      have hnone : ∀ k, k < m →
          evalOriginalActionCode R k (Encodable.encode s) = none := by
        apply evalOriginalActionCode_none_before R s (originalUpdate workspace) ha
        intro k hk hEq
        exact Nat.not_lt_of_ge (Nat.find_min' hp (by simpa [p] using hEq)) hk
      obtain ⟨nt,tail,he⟩ := ih
      have hterminal : Run (originalNativeControlCode R) (originalControl s m)
          s.epoch r (.update s.epoch :: nt) o := by
        have hup : originalNativeControlCode R (originalControl s m) =
            .applyRho (originalControl (afterOriginalUpdate s workspace) 0) := by
          have hm' :
              (Nat.Partrec.Code.evaln (2^m) R.code (Encodable.encode s)).bind
                  (fun n => @Encodable.decode (OriginalAction O) _ n) = some (originalUpdate workspace) := by
            simpa [evalOriginalActionCode, evalOriginalActionFromCode] using hm
          simp only [originalNativeControlCode, originalNativeControlFromCode,
            evalOriginalActionCode, evalOriginalActionFromCode, originalControl,
            Nat.unpair_pair]
          rw [Encodable.encodek, hm']
          rfl
        apply Run.update hup
        simpa [afterOriginalUpdate, OriginalState.epoch] using tail
      refine ⟨List.replicate m .localStep ++ (.update s.epoch :: nt), ?_, ?_⟩
      · exact original_code_native_prefix R s r hterminal hnone
      · simp [eraseEvaluatorSteps, he]
  | @read s r t o a cont y ha hy runTail ih =>
      obtain ⟨f,hf⟩ := evalOriginalActionCode_complete R s ha
      let p : Nat → Prop := fun j =>
        evalOriginalActionCode R j (Encodable.encode s) = some (originalRead a cont)
      have hp : ∃ k, p k := ⟨f,hf⟩
      let m := Nat.find hp
      have hm : p m := Nat.find_spec hp
      dsimp [p] at hm
      have hnone : ∀ k, k < m →
          evalOriginalActionCode R k (Encodable.encode s) = none := by
        apply evalOriginalActionCode_none_before R s (originalRead a cont) ha
        intro j hj hEq
        exact Nat.not_lt_of_ge (Nat.find_min' hp (by simpa [p] using hEq)) hj
      obtain ⟨nt,tail,he⟩ := ih
      have hterminal : Run (originalNativeControlCode R) (originalControl s m)
          s.epoch r (.read s.epoch a y :: nt) o := by
        have hr : originalNativeControlCode R (originalControl s m) =
            .read a (fun z =>
              originalControl (afterOriginalRead s a z (originalContinuation cont z)) 0) := by
          have hm' :
              (Nat.Partrec.Code.evaln (2^m) R.code (Encodable.encode s)).bind
                  (fun n => @Encodable.decode (OriginalAction O) _ n) = some (originalRead a cont) := by
            simpa [evalOriginalActionCode, evalOriginalActionFromCode] using hm
          simp only [originalNativeControlCode, originalNativeControlFromCode,
            evalOriginalActionCode, evalOriginalActionFromCode, originalControl,
            Nat.unpair_pair]
          rw [Encodable.encodek, hm']
          rfl
        apply Run.read hr hy
        simpa [afterOriginalRead, OriginalState.epoch] using tail
      refine ⟨List.replicate m .localStep ++ (.read s.epoch a y :: nt), ?_, ?_⟩
      · exact original_code_native_prefix R s r hterminal hnone
      · simp [eraseEvaluatorSteps, he]

private theorem erased_reads (t : Trace) : reads (eraseEvaluatorSteps t) = reads t := by
  induction t with
  | nil => rfl
  | cons e t ih => cases e <;> simpa [eraseEvaluatorSteps, reads] using ih

/-- The external observation includes the absorbing Halt and its entire output. -/
inductive ExternalObservation (O : Type) where
  | update : Nat → ExternalObservation O
  | read : Nat → Address → Reply → ExternalObservation O
  | halt : O → ExternalObservation O
  deriving DecidableEq

def externalEvents {O : Type} : Trace → List (ExternalObservation O)
  | [] => []
  | .localStep :: t => externalEvents t
  | .update n :: t => .update n :: externalEvents t
  | .read n a y :: t => .read n a y :: externalEvents t

def terminalObservation {O : Type} (t : Trace) (o : O) : List (ExternalObservation O) :=
  externalEvents t ++ [.halt o]

private theorem erased_external {O : Type} (t : Trace) :
    externalEvents (O := O) (eraseEvaluatorSteps t) = externalEvents t := by
  induction t with
  | nil => rfl
  | cons e t ih => cases e <;> simpa [eraseEvaluatorSteps, externalEvents] using ih

/-- A single source selector program represents all its terminating executions.
Local evaluator work adds no physical events, calls, or terminal observations. -/
theorem original_service_simulation {O : Type} [Primcodable O]
    (S : OriginalEffectiveService O) {s : OriginalState} {r : Source}
    {t : Trace} {o : O} (run : OriginalRun S s r t o) :
    Computable₂ (evalOriginalAction S) ∧
    ∃ nt, Run (originalNativeControl S) (originalControl s 0) s.epoch r nt o ∧
      eraseEvaluatorSteps nt = t ∧ reads nt = reads t ∧
      terminalObservation nt o = terminalObservation t o := by
  refine ⟨evalOriginalAction_effective S, ?_⟩
  obtain ⟨nt,hn,he⟩ := original_run_to_native S run
  refine ⟨nt,hn,he,?_,?_⟩
  · rw [← erased_reads nt, he]
  · unfold terminalObservation
    rw [← erased_external nt, he]

theorem original_code_service_simulation {O : Type} [Primcodable O]
    {S : OriginalEffectiveService O} (R : OriginalCodeRealization S)
    {s : OriginalState} {r : Source} {t : Trace} {o : O}
    (run : OriginalRun S s r t o) :
    Computable₂ (evalOriginalActionCode R) ∧
      ∃ nt, Run (originalNativeControlCode R) (originalControl s 0) s.epoch r nt o ∧
        eraseEvaluatorSteps nt = t ∧ reads nt = reads t ∧
        terminalObservation nt o = terminalObservation t o := by
  have effective : Computable₂ (evalOriginalActionCode R) := by
    apply Computable.option_bind
      (Nat.Partrec.Code.primrec_evaln.to_comp.comp
        (((((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst).to_comp).pair (Computable.const R.code)).pair Computable.snd))
    exact (Computable.decode.comp Computable.snd).to₂
  refine ⟨effective, ?_⟩
  obtain ⟨nt,hn,he⟩ := original_code_run_to_native R run
  refine ⟨nt,hn,he,?_,?_⟩
  · rw [← erased_reads nt, he]
  · unfold terminalObservation
    rw [← erased_external nt, he]

/-- One encoded machine configuration is an arbitrary natural number. The
packet contains an opcode, successor/output code, address and four continuations.
No finite state, workspace, address, runtime or update bound is imposed. -/
abbrev Packet := Nat × Nat × Address × (Nat × Nat × Nat × Nat)

/-- A total computable one-step interpreter. Divergent local computation is
represented by arbitrarily many machine steps, not a total boundary oracle. -/
structure EffectiveService (O : Type) where
  tick : Nat → Packet
  effective : Computable tick
  initial : Nat
  output : Nat → O

def continuation (p : Packet) : Reply → Nat
  | .alpha => p.2.2.2.1
  | .beta => p.2.2.2.2.1
  | .branch => p.2.2.2.2.2.1
  | .absent => p.2.2.2.2.2.2

/-- Compilation expands only the four external instruction cases. It does not
run local computation to a boundary or precompile an observation tree. -/
def compile {O : Type} (S : EffectiveService O) (c : Nat) : Op Nat O :=
  let p := S.tick c
  if p.1 = 0 then .localStep p.2.1
  else if p.1 = 1 then .read p.2.2.1 (continuation p)
  else if p.1 = 2 then .applyRho p.2.1
  else .stop (S.output p.2.1)

/-- Direct operational semantics of the encoded service and its original
physical register. Events and terminal output are complete, not comparison bits. -/
inductive ServiceRun {O : Type} (S : EffectiveService O) :
    Nat → Nat → Source → Trace → O → Prop
  | localStep {c e r t o} : (S.tick c).1 = 0 →
      ServiceRun S (S.tick c).2.1 e r t o →
      ServiceRun S c e r (.localStep :: t) o
  | read {c e r y t o} : (S.tick c).1 = 1 →
      readout (S.tick c).2.2.1 r = y →
      ServiceRun S (continuation (S.tick c) y) e r t o →
      ServiceRun S c e r (.read e (S.tick c).2.2.1 y :: t) o
  | update {c e r t o} : (S.tick c).1 = 2 →
      ServiceRun S (S.tick c).2.1 (e+1) (substitution r) t o →
      ServiceRun S c e r (.update e :: t) o
  | stop {c e r} : (S.tick c).1 ≠ 0 → (S.tick c).1 ≠ 1 → (S.tick c).1 ≠ 2 →
      ServiceRun S c e r [] (S.output (S.tick c).2.1)

/-- Every terminating original encoded service has exactly the same physical
trace, epochs, chronological Read count and entire output in the broader class. -/
theorem effective_service_inclusion {O : Type} (S : EffectiveService O)
    {c e : Nat} {r : Source} {t : Trace} {o : O}
    (run : ServiceRun S c e r t o) : Run (compile S) c e r t o := by
  induction run with
  | localStep h run ih => exact Run.localStep (by simp [compile,h]) ih
  | read h hy run ih => exact Run.read (by simp [compile,h]) hy ih
  | update h run ih => exact Run.update (by simp [compile,h]) ih
  | stop h0 h1 h2 => exact Run.stop (by simp [compile,h0,h1,h2])

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
