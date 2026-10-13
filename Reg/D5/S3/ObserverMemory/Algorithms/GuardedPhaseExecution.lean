import D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

@[reducible] def signature : Signature where
  Params := Σ Q : Type u, Σ A : Type v, Σ R : Type w,
    Σ _prog : Q → Instruction Q A R, Σ _x : Q, Σ _h : Q, Σ _a : Nat, Nat
  State p := Nat → p.2.1 → p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Classical truth reification observes every finite-run proposition; it is not
an effective decision procedure for arbitrary instruction and observation types. -/
def actual : Realization signature.{u,v,w} := by
  classical
  exact realize signature.{u,v,w}
    (fun _ ⟨_Q, _A, _R, prog, x, h, a, J⟩ obs => decide (Run prog obs x a h J))
    (fun e => nomatch e)

def rejected : Realization signature.{u,v,w} := realize signature.{u,v,w}
  (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u,v,w}
  Law F := ∀ {Q : Type u} {A : Type v} {R : Type w}
    {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {x h : Q} {a J : Nat} {blocks : List (Nat × (A → R))}
    (_partition : Partition obs a (J + 1) blocks),
    PhasePaths prog x a h J blocks ↔ F.readout () ⟨Q, A, R, prog, x, h, a, J⟩ obs = true

private theorem positive : arena.{u,v,w}.Law actual.{u,v,w} := by
  classical
  intro Q A R prog obs x h a J blocks partition
  simpa [actual, realize] using guarded_phase_execution partition

private theorem negative : ¬ arena.{u,v,w}.Law rejected.{u,v,w} := by
  intro law
  have bad := @law (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit)
    (fun _ => .halt) (fun _ _ => ⟨()⟩) ⟨()⟩ ⟨()⟩ 0 0 [(1, fun _ => ⟨()⟩)]
    ⟨by omega, rfl, by intro j hj hk; rfl⟩
  have impossible := bad.mp ⟨rfl, FixedPath.refl _⟩
  cases impossible

private def probeProg (x : ULift.{u} Bool) :
    Instruction (ULift.{u} Bool) (ULift.{v} Unit) (ULift.{w} Bool) :=
  if x.down then .halt else .read ⟨()⟩ (fun r => ⟨r.down⟩)

private theorem false_invariant {x y : ULift.{u} Bool} {a b : Nat}
    (path : Run probeProg (fun _ _ => (⟨false⟩ : ULift.{w} Bool)) x a y b) :
    x.down = false → y.down = false := by
  induction path with
  | refl => exact id
  | read hop tail ih =>
      intro hx
      simp only [probeProg, hx, Bool.false_eq_true, if_false] at hop
      cases hop
      exact ih rfl
  | update hop tail ih =>
      intro hx
      simp [probeProg, hx] at hop

def evidence : Registration arena.{u,v,w}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.guarded_phase_execution.{u,v,w})) where
  actual := actual
  bridge := by
    classical
    simp [arena, actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Unit, ULift.{w} Bool,
      probeProg, ⟨false⟩, ⟨true⟩, 0, 0⟩,
      (fun _ _ => ⟨true⟩), (fun _ _ => ⟨false⟩), ?_⟩
    change decide (Run probeProg (fun _ _ => (⟨true⟩ : ULift.{w} Bool)) ⟨false⟩ 0 ⟨true⟩ 0) ≠
      decide (Run probeProg (fun _ _ => (⟨false⟩ : ULift.{w} Bool)) ⟨false⟩ 0 ⟨true⟩ 0)
    intro same
    have good : Run probeProg (fun _ _ => (⟨true⟩ : ULift.{w} Bool))
        ⟨false⟩ 0 ⟨true⟩ 0 := .read rfl (.refl _ _)
    have bad := of_decide_eq_true (same.symm.trans (decide_eq_true good))
    have impossible := false_invariant bad rfl
    cases impossible

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.guarded_phase_execution.{u,v,w})
    (type_of% (realize signature.{u,v,w} actual.{u,v,w}.readout actual.{u,v,w}.anchor))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.guarded_phase_execution,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.evidence,
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
    owner := `D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution,
    definition := none,
    coordinates := #[0, 1, 2, 3, 5, 6, 7, 8],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "fn", "fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
