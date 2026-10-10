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
