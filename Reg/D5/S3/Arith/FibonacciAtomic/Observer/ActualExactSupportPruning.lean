import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning
open D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable
open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Strategy)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning
universe u

structure Context where
  Carrier : Type u
  finite : Fintype Carrier
  support : Finset Address
  observer : @Observer Carrier finite

abbrev signature : Signature where
  Params := Context.{u}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := @Observer p.Carrier p.finite
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ p _ => @supportObserver p.Carrier p.finite p.support p.observer)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (N : Nat) (Q : Finset Address) (M : Observer E),
    Admissible N M → (∀ U, Allowed N U → ActualSupport Q M U) →
    (∀ U, Allowed N U → ∀ e h,
      ActualPrefix (R.readout () ⟨E, inferInstance, Q, M⟩ ()) U e h ↔
        ActualPrefix M U e h) ∧
    (∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
      (R.readout () ⟨E, inferInstance, Q, M⟩ ()).decoder e = M.decoder e) ∧
    (∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
      (R.readout () ⟨E, inferInstance, Q, M⟩ ()).action e = M.action e) ∧
    (∀ U, Allowed N U → ∀ t f b, Run M U M.e0 t f b →
      Run (R.readout () ⟨E, inferInstance, Q, M⟩ ()) U M.e0 t f b) ∧
    Admissible N (R.readout () ⟨E, inferInstance, Q, M⟩ ())

theorem bridge : (type_of% (@support_pruning_contract.{u})) ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h E finite N Q M admissible supported
    have r := h N Q M admissible supported
    exact ⟨r.prefixes, r.cache, r.actions, r.runs, r.admissible⟩
  · intro h E finite N Q M admissible supported
    obtain ⟨prefixes, cache, actions, runs, adm⟩ := h N Q M admissible supported
    exact ⟨prefixes, cache, actions, runs, adm⟩

theorem actual_law : arena.{u}.Law actual.{u} := bridge.mp (@support_pruning_contract.{u})

theorem no_dependence : ¬ ObservationalDependence signature.{u} actual.{u} := by
  rintro h
  obtain ⟨p, x, y, different⟩ := h ()
  exact different (congrArg (actual.readout () p) (Subsingleton.elim x y))

structure TableContext where
  N : Nat
  strategy : Strategy
  count : Nat
  positive : 0 < count

abbrev tableSignature : Signature where
  Params := TableContext
  State p := NativeTable (supportWidth (prescribedSupport p.N p.strategy)) p.count
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Observer (Fin p.count)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def tableActual : Realization tableSignature :=
  realize tableSignature (fun _ p T => tableObserver p.positive T) (fun e => nomatch e)

abbrev tableArena : Arena where
  signature := tableSignature
  Law R := ∀ {E : Type u} [Fintype E] (N : Nat) (π : Strategy) (M : Observer E),
    Admissible N M → ExactTraces N π M →
    ∃ (positive : 0 < Fintype.card E) (r : E ≃ Fin (Fintype.card E))
      (T : NativeTable (supportWidth (prescribedSupport N π)) (Fintype.card E)),
      Admissible N (R.readout () ⟨N, π, Fintype.card E, positive⟩ T) ∧
      ExactTraces N π (R.readout () ⟨N, π, Fintype.card E, positive⟩ T) ∧
      (∀ U, Allowed N U → ∀ e h,
        ActualPrefix (R.readout () ⟨N, π, Fintype.card E, positive⟩ T) U (r e) h ↔
          ActualPrefix M U e h) ∧
      (∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
        (R.readout () ⟨N, π, Fintype.card E, positive⟩ T).decoder (r e) = M.decoder e ∧
        (R.readout () ⟨N, π, Fintype.card E, positive⟩ T).action (r e) = M.action e) ∧
      (∀ e q, (R.readout () ⟨N, π, Fintype.card E, positive⟩ T).action e = .inl q →
        q ∈ prescribedSupport N π) ∧
      (∀ e a, a ∈ (R.readout () ⟨N, π, Fintype.card E, positive⟩ T).decoder e →
        a.1 ∈ prescribedSupport N π)

theorem table_bridge : (type_of% (@exact_competitor_table_coverage.{u})) ↔
    tableArena.{u}.Law tableActual := Iff.rfl

theorem table_law : tableArena.{u}.Law tableActual := @exact_competitor_table_coverage.{u}

#print axioms bridge
#print axioms actual_law
#print axioms no_dependence
#print axioms table_bridge
#print axioms table_law

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning
