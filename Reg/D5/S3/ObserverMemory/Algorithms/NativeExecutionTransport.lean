import D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport
import Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution

namespace Reg.D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

macro "oldProbe" : term =>
  pure (Lean.mkIdent ((`_private.Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution).num 0 ++
    `Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.probeProg))

macro "oldInvariant" : term =>
  pure (Lean.mkIdent ((`_private.Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution).num 0 ++
    `Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.false_invariant))

namespace Transport
universe u' v'

@[reducible] def signature : Signature where
  Params := Σ Q : Type u, Σ A : Type v, Σ R : Type w,
    Σ Q' : Type u', Σ A' : Type v', Σ _sigma : Q ≃ Q', Σ _f : A → A',
    Σ _prog : Q → Instruction Q A R, Σ _prog' : Q' → Instruction Q' A' R,
    Σ _obs : Nat → A → R, Σ _x : Q, Σ _y : Q, Σ _a : Nat, Nat
  State p := Nat → p.2.2.2.2.1 → p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w,u',v'} := by
  classical
  exact realize signature.{u,v,w,u',v'}
    (fun _ ⟨_Q, _A, _R, _Q', _A', sigma, _f, _prog, prog', _obs, x, y, a, b⟩ obs' =>
      decide (Run prog' obs' (sigma x) a (sigma y) b))
    (fun e => nomatch e)

def rejected : Realization signature.{u,v,w,u',v'} :=
  realize signature.{u,v,w,u',v'} (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u,v,w,u',v'}
  Law F := ∀ {Q : Type u} {A : Type v} {R : Type w} {Q' : Type u'} {A' : Type v'}
    (sigma : Q ≃ Q') (f : A → A')
    {prog : Q → Instruction Q A R} {prog' : Q' → Instruction Q' A' R}
    {obs : Nat → A → R} {obs' : Nat → A' → R}
    (_instructions : ∀ q, prog' (sigma q) = Instruction.transport sigma f (prog q))
    (_responses : ∀ j p, obs' j (f p) = obs j p) {x y : Q} {a b : Nat},
    Run prog obs x a y b ↔
      F.readout () ⟨Q, A, R, Q', A', sigma, f, prog, prog', obs, x, y, a, b⟩ obs' = true

private theorem positive : arena.{u,v,w,u',v'}.Law actual.{u,v,w,u',v'} := by
  classical
  intro Q A R Q' A' sigma f prog prog' obs obs' instructions responses x y a b
  simpa [actual, realize] using run_transport_iff sigma f instructions responses

private theorem negative : ¬ arena.{u,v,w,u',v'}.Law rejected.{u,v,w,u',v'} := by
  intro law
  let sigma : ULift.{u} Unit ≃ ULift.{u'} Unit := Equiv.ulift.trans Equiv.ulift.symm
  have bad := @law (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit)
    (ULift.{u'} Unit) (ULift.{v'} Unit) sigma (fun _ => ⟨()⟩)
    (fun _ => .halt) (fun _ => .halt) (fun _ _ => ⟨()⟩) (fun _ _ => ⟨()⟩)
    (by intro q; rfl) (by intro j p; rfl) ⟨()⟩ ⟨()⟩ 0 0
  have impossible := bad.mp (.refl _ _)
  cases impossible

def evidence : Registration arena.{u,v,w,u',v'}
    (type_of%
      (@run_transport_iff.{u,v,w,u',v'})) where
  actual := actual
  bridge := by
    classical
    simp [actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    let sigma : ULift.{u} Bool ≃ ULift.{u'} Bool := Equiv.ulift.trans Equiv.ulift.symm
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Unit, ULift.{w} Bool,
      ULift.{u'} Bool, ULift.{v'} Unit, sigma, (fun _ => ⟨()⟩), oldProbe,
      oldProbe, (fun _ _ => ⟨true⟩), ⟨false⟩, ⟨true⟩, 0, 0⟩,
      (fun _ _ => ⟨true⟩), (fun _ _ => ⟨false⟩), ?_⟩
    change decide (Run oldProbe (fun _ _ => (⟨true⟩ : ULift.{w} Bool)) ⟨false⟩ 0 ⟨true⟩ 0) ≠
      decide (Run oldProbe (fun _ _ => (⟨false⟩ : ULift.{w} Bool)) ⟨false⟩ 0 ⟨true⟩ 0)
    intro same
    have good : Run oldProbe (fun _ _ => (⟨true⟩ : ULift.{w} Bool))
        ⟨false⟩ 0 ⟨true⟩ 0 := .read rfl (.refl _ _)
    have bad := of_decide_eq_true (same.symm.trans (decide_eq_true good))
    cases oldInvariant bad rfl

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@run_transport_iff.{u,v,w,u',v'})
    (type_of% (realize signature.{u,v,w,u',v'}
      actual.{u,v,w,u',v'}.readout actual.{u,v,w,u',v'}.anchor))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport.run_transport_iff,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport.Transport.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u,v,w,u',v'}⟩, objectArena := .source ⟨arena.{u,v,w,u',v'}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u,v,w,u',v'} ⟨evidence.{u,v,w,u',v'}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,v,w,u',v'}
    actual.{u,v,w,u',v'}.readout actual.{u,v,w,u',v'}.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport,
    definition := none,
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "fn", "fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end Transport

namespace HaltUniqueness

/-- The intervention claims every selected left endpoint is reachable. -/
def rejected : Realization signature.{u,v,w} :=
  realize signature.{u,v,w} (fun _ _ _ => true) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u,v,w}
  Law F := ∀ {Q : Type u} {A : Type v} {R : Type w}
    {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {x h h' : Q} {a J J' : Nat}
    (_left : F.readout () ⟨Q, A, R, prog, x, h, a, J⟩ obs = true)
    (_right : Run prog obs x a h' J')
    (_halt : prog h = .halt) (_halt' : prog h' = .halt), h = h' ∧ J = J'

private theorem positive : arena.{u,v,w}.Law actual.{u,v,w} := by
  classical
  intro Q A R prog obs x h h' a J J' left right halt halt'
  exact run_halt_unique (of_decide_eq_true left) right halt halt'

private theorem negative : ¬ arena.{u,v,w}.Law rejected.{u,v,w} := by
  intro law
  have bad := @law (ULift.{u} Bool) (ULift.{v} Unit) (ULift.{w} Unit)
    (fun _ => .halt) (fun _ _ => ⟨()⟩) ⟨false⟩ ⟨true⟩ ⟨false⟩ 0 0 0
    rfl (.refl _ _) rfl rfl
  cases bad.1

def evidence : Registration arena.{u,v,w}
    (type_of%
      (@run_halt_unique.{u,v,w})) where
  actual := actual
  bridge := by
    classical
    simp [actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := _root_.Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.evidence.dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@run_halt_unique.{u,v,w})
    (type_of% (realize signature.{u,v,w} actual.{u,v,w}.readout actual.{u,v,w}.anchor))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport.run_halt_unique,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport.HaltUniqueness.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u,v,w}⟩, objectArena := .source ⟨arena.{u,v,w}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u,v,w} ⟨evidence.{u,v,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,v,w} actual.{u,v,w}.readout actual.{u,v,w}.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport,
    definition := none,
    coordinates := #[0, 1, 2, 3, 5, 6, 8, 9],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "domain"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "fn", "fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end HaltUniqueness

end
end Reg.D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport
