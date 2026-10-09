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
