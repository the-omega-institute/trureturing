import D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

@[reducible] def signature : Signature where
  Params := Nat
  State _ := FirstOrder.Language.presburger.Formula Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The audit observes path realization; its law preserves the entire two-part statement. -/
def actual : Realization signature := by
  classical
  exact realize signature
    (fun _ d formula => decide (formula.Realize (fun _ => d)))
    (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {Q : Type u} {A : Type v} {R : Type w} [finite : Fintype Q] [eq : DecidableEq Q]
    (prog : Q → Instruction Q A R) (reply : A → R) (x y : Q) (d : Nat),
    (F.readout () d (pathFormula prog reply x y) = true ↔
      FixedPath prog reply x y d) ∧
    ((crossingFormula prog reply x y).Realize (fun _ => d) ↔ Crossing prog reply x y d)

private theorem positive : arena.{u,v,w}.Law actual := by
  classical
  intro Q A R finite eq prog reply x y d
  simpa [actual, realize] using fixed_response_formulas_correct prog reply x y d

private theorem negative : ¬ arena.{u,v,w}.Law rejected := by
  intro law
  have impossible := (@law (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit)
    inferInstance inferInstance (fun _ => .halt) (fun _ => ⟨()⟩) ⟨()⟩ ⟨()⟩ 0).1.mpr (.refl _)
  cases impossible

def evidence : Registration arena.{u,v,w}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger.fixed_response_formulas_correct.{u,v,w})) where
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
    refine ⟨0, ⊤, ⊥, ?_⟩
    simp [actual, realize, FirstOrder.Language.Formula.Realize]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger.fixed_response_formulas_correct.{u,v,w})
    (type_of% (realize signature actual.readout actual.anchor))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger.fixed_response_formulas_correct,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u,v,w}⟩, objectArena := .source ⟨arena.{u,v,w}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u,v,w} ⟨evidence.{u,v,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger,
    definition := none,
    coordinates := #[9],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger
