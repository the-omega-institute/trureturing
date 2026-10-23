import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells InitialTailCost
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def signature : Signature where
  Params := Σ k : ℕ, Σ m : ℕ, Bool
  State p := List (AllowedBlock p.1 p.2.1 p.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ history => (historyRecord history).map LiveRecord.tail) (fun e => nomatch e)

def erased : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)

/-- The readout is the initial history target; the same actual executor and
both alphabets remain fixed throughout the complete budget statement. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) (alphabet : Bool) (n : ℕ),
    (∃ controller : Option (ZMod 2) → AcquisitionTree k m alphabet (Option ℕ) n,
      ∀ history : List (AllowedBlock k m alphabet),
        (controller (endpointReading (historyRecord history))).result (historyRecord history) =
          R.readout () ⟨k, m, alphabet⟩ history) ↔
      (m = 1 ∧ k - 1 ≤ n) ∨ (k = 2 ∧ 1 ≤ n)

private theorem positive : arena.Law actual := initial_tail_budget_exact

private theorem negative : ¬ arena.Law erased := by
  intro law
  have falseBudget := law 2 1 (by omega) (by omega) false 0
  have success : ∃ controller : Option (ZMod 2) → AcquisitionTree 2 1 false (Option ℕ) 0,
      ∀ history : List (AllowedBlock 2 1 false),
        (controller (endpointReading (historyRecord history))).result (historyRecord history) =
          erased.readout () ⟨2, 1, false⟩ history :=
    ⟨fun _ => .stop none, fun _ => rfl⟩
  have impossible := falseBudget.mp success
  omega

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost.initial_tail_budget_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, erased, negative⟩
  sensitivity := ⟨fun i => ⟨erased,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    let one : AllowedBlock 2 1 false := ⟨fun _ => true, fun h => Bool.noConfusion h⟩
    refine ⟨⟨2, 1, false⟩, [], [one, one], ?_⟩
    change (some (0 : ℕ)) ≠ none
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost.initial_tail_budget_exact)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost.initial_tail_budget_exact
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost/\
    Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost,
    definition := none,
    coordinates := #[0, 1, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg",
        "body", "body", "arg"],
      stateBinder := 7,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence

end

end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost
