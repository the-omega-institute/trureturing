import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning
open D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable
open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply Strategy)
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
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

abbrev tailSignature : Signature where
  Params := RawHistory
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RawHistory
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def tailActual : Realization tailSignature :=
  realize tailSignature (fun _ h s => h ++ s) (fun e => nomatch e)

abbrev tailArena : Arena where
  signature := tailSignature
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (U : Source)
    {e : E} {h : RawHistory}, ActualPrefix M U e h →
    ∀ {t : RawHistory} {f : E} {b : Bool}, Run M U M.e0 t f b →
      ∃ s, Run M U e s f b ∧ R.readout () h s = t

theorem tail_bridge : (type_of% (@prefix_run_tail.{u})) ↔ tailArena.{u}.Law tailActual := Iff.rfl

theorem tail_law : tailArena.{u}.Law tailActual := @prefix_run_tail.{u}

theorem tail_dependence : ObservationalDependence tailSignature tailActual := by
  intro i
  exact ⟨[], [], [⟨[], Reply.absent⟩], by simp [tailActual, realize]⟩

#print axioms tail_bridge
#print axioms tail_law
#print axioms tail_dependence

private def haltObserver : Observer (ULift.{u} Unit) where
  e0 := ⟨()⟩
  action _ := .inr false
  transition e _ := e
  decoder _ := []
  decoded_nodup _ := by simp

noncomputable def tailBad : Realization tailSignature :=
  realize tailSignature (fun _ _ _ => [⟨[], Reply.absent⟩]) (fun e => nomatch e)

theorem tail_bad : ¬ tailArena.{u}.Law tailBad := by
  intro law
  obtain ⟨s, _, impossible⟩ := law haltObserver (.of false)
    ActualPrefix.initial (Run.halt (b := false) rfl)
  change ([⟨[], Reply.absent⟩] : RawHistory) = [] at impossible
  cases impossible

theorem tail_variation : Variation tailArena.{u} tailActual := ⟨tail_law, tailBad, tail_bad⟩

theorem tail_sensitivity : Sensitivity tailArena.{u} tailActual := by
  constructor
  · intro i
    refine ⟨tailBad, ?_, ?_, tail_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

noncomputable def tailFamily : Registration tailArena.{u} (type_of% (@prefix_run_tail.{u})) where
  actual := tailActual
  bridge := tail_bridge
  variation := tail_variation
  sensitivity := tail_sensitivity
  dependence := tail_dependence

#print axioms tailFamily

noncomputable def tailRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@prefix_run_tail.{u}) (Realization tailSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning.tailUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning.tailFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena.{u}⟩
  objectArena := .source ⟨tailArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source tailArena.{u} ⟨tailFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize tailSignature tailActual.readout tailActual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms tailRegistration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning
