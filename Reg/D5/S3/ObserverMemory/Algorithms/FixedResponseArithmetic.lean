import D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

@[reducible] def signature : Signature where
  Params := Σ Q : Type u, Σ _y : Q, Nat
  State p := List (Record p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Truth reification belongs to the audit; the source coefficients are executable. -/
def actual : Realization signature.{u} := by
  classical
  exact realize signature.{u}
    (fun _ ⟨_Q, y, d⟩ data => decide (Supports data y d))
    (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law F := ∀ {Q : Type u} {A : Type v} {R : Type w} [finite : Fintype Q] [eq : DecidableEq Q]
    (prog : Q → Instruction Q A R) (reply : A → R) (x y : Q) (d : Nat),
    FixedPath prog reply x y d ↔ F.readout () ⟨Q, y, d⟩ (records prog reply x) = true

private theorem positive : arena.{u,v,w}.Law actual.{u} := by
  classical
  intro Q A R finite eq prog reply x y d
  simpa [actual, realize] using fixed_path_iff_support prog reply x y d

private theorem negative : ¬ arena.{u,v,w}.Law rejected.{u} := by
  intro law
  have impossible := (@law (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit)
    inferInstance inferInstance (fun _ => .halt) (fun _ => ⟨()⟩) ⟨()⟩ ⟨()⟩ 0).mp (.refl _)
  cases impossible

def evidence : Registration arena.{u,v,w}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic.fixed_path_iff_support.{u,v,w})) where
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
    refine ⟨⟨ULift.{u} Unit, ⟨()⟩, 0⟩, [⟨some ⟨()⟩, 0, 0⟩], [], ?_⟩
    simp [actual, realize, Supports]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic.fixed_path_iff_support.{u,v,w})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic.fixed_path_iff_support,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u,v,w}⟩, objectArena := .source ⟨arena.{u,v,w}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u,v,w} ⟨evidence.{u,v,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic,
    definition := none,
    coordinates := #[0, 8, 9],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic
