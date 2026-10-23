import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable
open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination (Observer)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable
universe u

structure Context where
  Carrier : Type u
  finite : Fintype Carrier
  observer : @Observer Carrier finite

abbrev signature : Signature where
  Params := Context.{u}
  State p := p.Carrier ≃ Fin (@Fintype.card p.Carrier p.finite)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Observer (Fin (@Fintype.card p.Carrier p.finite))
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ p r => @relabel p.Carrier p.finite _ p.observer r)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (N : Nat) (M : Observer E)
    (positive : 0 < Fintype.card E) (r : E ≃ Fin (Fintype.card E))
    (T : NativeTable N (Fintype.card E)), r M.e0 = ⟨0, positive⟩ →
    tableObserver positive T = R.readout () ⟨E, inferInstance, M⟩ r →
    RepresentationContract N M positive r T

theorem bridge : (type_of% (@representation_contract.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
theorem actual_law : arena.{u}.Law actual.{u} := @representation_contract.{u}

#print axioms bridge
#print axioms actual_law

abbrev halted (b : Bool) : @Observer (ULift.{u} Unit) inferInstance where
  e0 := ⟨()⟩
  action _ := .inr b
  transition e _ := e
  decoder _ := []
  decoded_nodup _ := List.nodup_nil

noncomputable def rejected : Realization signature.{u} :=
  realize signature (fun _ p r =>
    { @relabel p.Carrier p.finite _ p.observer r with action := fun _ => .inr false })
    (fun e => nomatch e)

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  classical
  intro h
  obtain ⟨positive, r, T, initial, table⟩ := bounded_table_representation 1 (halted.{u} false)
    (by intro e q row; cases row) (by intro e a member; cases member)
  have matching : tableObserver positive T =
      rejected.readout () ⟨ULift.{u} Unit, inferInstance, halted true⟩ r := by
    rw [table]
    rfl
  have contract := h 1 (halted true) positive r T initial matching
  have bad := contract.actions (ULift.up ())
  rw [table] at bad
  change Sum.inr false = Sum.inr true at bad
  cases bad

noncomputable def representationProof : Registration arena.{u} (type_of% (@representation_contract.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    let M : @Observer (ULift.{u} Bool) inferInstance := {
      e0 := ⟨false⟩, action := fun _ => .inr false,
      transition := fun e _ => e, decoder := fun _ => [],
      decoded_nodup := fun _ => List.nodup_nil }
    let r := Fintype.equivFin (ULift.{u} Bool)
    let s := (Equiv.swap (ULift.up false) (ULift.up true)).trans r
    refine ⟨⟨ULift.{u} Bool, inferInstance, M⟩, r, s, ?_⟩
    intro equal
    have initial := congrArg Observer.e0 equal
    change r (ULift.up false) = r (Equiv.swap (ULift.up false) (ULift.up true) (ULift.up false)) at initial
    rw [Equiv.swap_apply_left] at initial
    have bad := congrArg ULift.down (r.injective initial)
    cases bad

#print axioms representationProof




abbrev operatorSignature : Signature where
  Params := Type u
  State _ := type_of% (@relabel.{u})
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := type_of% (@relabel.{u} E)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev operatorActual : Realization operatorSignature.{u} :=
  realize operatorSignature (fun _ E f => @f E) (fun e => nomatch e)

abbrev operatorArena : Arena where
  signature := operatorSignature.{u}
  Law R := ∀ {E : Type u} [i : Fintype E] (N : Nat) (M : @Observer E i)
    (positive : 0 < @Fintype.card E i) (r : E ≃ Fin (@Fintype.card E i))
    (T : NativeTable N (@Fintype.card E i)) (initial : r M.e0 = ⟨0, positive⟩)
    (table : tableObserver positive T =
      @Realization.readout operatorSignature.{u} R () E (@relabel.{u})
        i (@Fintype.card E i) M r),
    @RepresentationContract E i N M positive r T

theorem operatorBridge : (type_of% (@representation_contract.{u})) ↔
    operatorArena.{u}.Law operatorActual.{u} := Iff.rfl

theorem operatorActualLaw : operatorArena.{u}.Law operatorActual.{u} :=
  @representation_contract.{u}

def rejectedOperator : type_of% (@relabel.{u}) :=
  fun {A} [j : Fintype A] {n} M r =>
    { @relabel.{u} A j n M r with action := fun _ => .inr false }

abbrev operatorRejected : Realization operatorSignature.{u} :=
  realize operatorSignature (fun _ E _ => @rejectedOperator.{u} E)
    (fun e => nomatch e)

theorem operatorRejectedLaw : ¬ operatorArena.{u}.Law operatorRejected.{u} :=
  rejected_law

theorem operatorDependence : ObservationalDependence operatorSignature.{u} operatorActual.{u} := by
  classical
  intro i
  let E := ULift.{u} Unit
  let r := Fintype.equivFin E
  refine ⟨E, @relabel.{u}, @rejectedOperator.{u}, ?_⟩
  intro equal
  have applied := congrArg (fun f => @f inferInstance (Fintype.card E) (halted true) r) equal
  have actions := congrArg (fun M => M.action (r (ULift.up ()))) applied
  change Sum.inr true = Sum.inr false at actions
  cases actions

theorem operatorSensitivity : Sensitivity operatorArena.{u} operatorActual.{u} :=
  ⟨fun i => ⟨operatorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, operatorRejectedLaw⟩,
    fun i => nomatch i⟩

noncomputable def operatorRepresentationProof :
    Registration operatorArena.{u} (type_of% (@representation_contract.{u})) where
  actual := operatorActual
  bridge := operatorBridge
  variation := ⟨operatorActualLaw, operatorRejected, operatorRejectedLaw⟩
  sensitivity := operatorSensitivity
  dependence := operatorDependence

#print axioms operatorBridge
#print axioms operatorActualLaw
#print axioms operatorRejectedLaw
#print axioms operatorDependence
#print axioms operatorSensitivity
#print axioms operatorRepresentationProof

noncomputable def representation_contract_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable.representation_contract.{u}) (Realization operatorArena.{u}.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable.representation_contract
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable.operatorRepresentationProof
  realizationSource := none
  generated := false
  arena := .source ⟨operatorArena⟩
  objectArena := .source ⟨operatorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source operatorArena ⟨operatorRepresentationProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize operatorArena.signature operatorActual.readout operatorActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg", "fn", "fn", "fn", "fn"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms representation_contract_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable.Exports
universe u
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization (Fee)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Context where
  Carrier : Type u
  finite : Fintype Carrier
  n : Nat
  observer : @Observer Carrier finite

abbrev signature : Signature where
  Params := Context.{u}
  State p := p.Carrier ≃ Fin p.n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Observer (Fin p.n)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ p r => @relabel p.Carrier p.finite p.n p.observer r)
    (fun e => nomatch e)

abbrev admissibleArena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Fintype E] {n : Nat} (N : Nat) (M : Observer E)
    (r : E ≃ Fin n), Admissible N M →
      Admissible N (R.readout () ⟨E, inferInstance, n, M⟩ r)

abbrev feeArena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Fintype E] {n : Nat} (M : Observer E)
    (r : E ≃ Fin n) (tau : Address → ℝ) (U : Source),
      Fee (R.readout () ⟨E, inferInstance, n, M⟩ r) tau U = Fee M tau U

theorem admissibleBridge : (type_of% (@relabel_admissible.{u})) ↔
    admissibleArena.{u}.Law actual.{u} := Iff.rfl
theorem admissibleLaw : admissibleArena.{u}.Law actual.{u} := @relabel_admissible.{u}
theorem feeBridge : (type_of% (@relabel_fee.{u})) ↔ feeArena.{u}.Law actual.{u} := Iff.rfl
theorem feeLaw : feeArena.{u}.Law actual.{u} := @relabel_fee.{u}

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable.Exports
