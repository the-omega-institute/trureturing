import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.NativeCompletedHistoryRecovery
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution composition)
open _root_.D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution
open _root_.D5.S3.Arith.FibonacciAtomic.NativeCompletedHistoryRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.NativeCompletedHistoryRecovery
noncomputable section

abbrev signature : Signature where
  Params := Nat
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (Source × List Letter)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature (fun _ n0 z => recover n0 z) (fun e => nomatch e)
abbrev rejected : Realization signature := realize signature (fun _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A :=     (∀ (n0 : Nat) (z t : Source) (W : List Letter),
      A.readout () n0 z = some (t,W) ↔
        1 < n0 ∧
        (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
          Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) ∧
        eventIndex t = n0 ∧ run t W = z) ∧
    (∀ (n0 : Nat) (z : Source),
      recover n0 z = none ↔
        ¬ ∃ (t : Source) (W : List Letter),
          1 < n0 ∧
        (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
          Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) ∧
        eventIndex t = n0 ∧ run t W = z) ∧
    (∀ (n0 : Nat) (z t : Source) (W : List Letter),
      recover n0 z = some (t,W) →
        W.length ≤ eventIndex z - n0 ∧ recoverySteps n0 z = W.length) ∧
    (∀ (n0 : Nat) (z p : Source) (X : Letter), Native z →
      previous n0 z = some (p,X) →
        Native p ∧ act X p = z ∧ eventIndex p < eventIndex z) ∧
    (∀ (n0 : Nat), 1 < n0 → ∀ (s t : Source),
      (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
        Geometry.NativeGuardedLeafRepair.run (.of true) cs = some s) →
      (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
        Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) →
      eventIndex s = n0 → eventIndex t = n0 → ∀ (V W : List Letter),
        run s V = run t W → s = t ∧ V = W) ∧
    (∀ W : List Letter, run (.of false) W = .of false ↔ W = []) ∧
    (∀ z : Source, (∃ W : List Letter, W ≠ [] ∧ run (.of false) W = z) →
      ∃! U : List Letter, recover 2 z = some (K,U) ∧
        ∀ W : List Letter, run (.of false) W = z ↔ W = .F :: U ∨ W = .G :: U) ∧
    (∀ (A : Type) (E : List Letter → A) (U : List Letter),
      (∃ D : A → List Letter, ∀ W : List Letter,
        run (.of false) W = run K U → D (E W) = W) ↔
          E (.F :: U) ≠ E (.G :: U)) ∧
    (∀ (t : Source) (es : List NativeLocalSourceExecution.Event),
      NativeLocalSourceExecution.replay t es =
        Geometry.NativeGuardedLeafRepair.run t (es.map toCall)) ∧
    (∀ t : Source, Native t ↔
      (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
        Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) ∧ t ≠ .of true) ∧
    (∀ (t : Source) (W : List Letter), Native t →
      Geometry.NativeGuardedLeafRepair.run t (primitiveWord t W) = some (run t W) ∧
      (primitiveWord t W).length = eventIndex (run t W) - eventIndex t) ∧
    (∀ (t : Source) (W : List Letter), Native t →
      ∀ (labels : Geometry.NativeGuardedLeafRepair.RawMap) (next : ℤ)
        (x : Geometry.NativeGuardedLeafRepair.Value),
      ∃ (labels' : Geometry.NativeGuardedLeafRepair.RawMap) (next' : ℤ)
        (y : Geometry.NativeGuardedLeafRepair.Value),
        Geometry.NativeGuardedLeafRepair.nativeRun t labels next x (primitiveWord t W) =
          some (run t W,labels',next',y) ∧
        (∀ p : NativeLocalSourceExecution.Address,
        p ∈ Geometry.NativeMaterialRootRecognition.material t → y p = x p) ∧
        (∀ p : NativeLocalSourceExecution.Address,
          p ∈ Geometry.NativeMaterialRootRecognition.material (run t W) →
          p ∉ Geometry.NativeMaterialRootRecognition.material t → y p = 0)) ∧
    (∀ U : List Letter,
      ∃ D : Bool → List Letter, ∀ W : List Letter,
        run (.of false) W = run K U → D (firstChoice W) = W) ∧
    (∀ (n0 : Nat) (z : Source), recoverySteps n0 z ≤ eventIndex z - n0)

private theorem actual_law : arena.Law actual := by exact completed_history_recovery

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := (law.1 2 K K []).mpr ⟨by decide,⟨[.promote [],.split []],rfl⟩,rfl,rfl⟩
  change (none : Option (Source × List Letter)) = some (K,[]) at impossible
  cases impossible

def evidence : Registration arena (type_of% (@completed_history_recovery)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨2, K, .of false, ?_⟩
    intro eq
    have good : recover 2 K = some (K,[]) :=
      (completed_history_recovery.1 2 K K []).mpr ⟨by decide,⟨[.promote [],.split []],rfl⟩,rfl,rfl⟩
    have bad : recover 2 (.of false) = none := rfl
    change recover 2 K = recover 2 (.of false) at eq
    rw [good,bad] at eq
    cases eq

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completed_history_recovery) (Realization signature) (Unit → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeCompletedHistoryRecovery.completed_history_recovery.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeCompletedHistoryRecovery.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence,objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n0 z => recover n0 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeCompletedHistoryRecovery
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn","arg","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end

end Reg.D5.S3.Arith.FibonacciAtomic.NativeCompletedHistoryRecovery
