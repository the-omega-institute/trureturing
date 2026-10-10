import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler
open D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization (allowedSources)
open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply Strategy terminal)
open D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory (kappa_hist)
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler

abbrev Budget := {N : Nat // 1 ≤ N}

abbrev countSignature : Signature where
  Params := Unit
  State _ := Nat × Strategy
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def countActual : Realization countSignature :=
  realize countSignature (fun _ _ p => Fintype.card (ExactState (strategyPrefixes p.1 p.2)))
    (fun e => nomatch e)

abbrev countArena : Arena where
  signature := countSignature
  Law R := ∀ N π, R.readout () () (N, π) = strategyStateCard N π

abbrev boundArena : Arena where
  signature := countSignature
  Law R := ∀ N π H (Q : Finset Address),
    (∀ U : Source, Allowed N U → (terminal π U).1.length ≤ H) →
    (∀ U : Source, Allowed N U → ∀ a ∈ (terminal π U).1, a.1 ∈ Q) →
    R.readout () () (N, π) ≤ 1 + (allowedSources N).card * (H + 1) * 2 ^ min Q.card H

abbrev observerSignature : Signature where
  Params := Budget × Strategy
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Observer (ExactState (strategyPrefixes p.1.val p.2))
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def observerActual : Realization observerSignature :=
  realize observerSignature (fun _ p _ => strategyObserver p.1.val p.2 p.1.property)
    (fun e => nomatch e)

abbrev admissibleArena : Arena where
  signature := observerSignature
  Law R := ∀ (N : Nat) (π : Strategy) (positive : 1 ≤ N),
    Function.FactorsThrough π.policy kappa_hist → Admissible N (R.readout () (⟨N, positive⟩, π) ())

abbrev runArena : Arena where
  signature := observerSignature
  Law R := ∀ (N : Nat) (π : Strategy) (positive : 1 ≤ N),
    Function.FactorsThrough π.policy kappa_hist → ∀ U : Source, Allowed N U →
      ∃ f, Run (R.readout () (⟨N, positive⟩, π) ()) U
        (R.readout () (⟨N, positive⟩, π) ()).e0 (terminal π U).1 f (terminal π U).2

abbrev prefixSignature : Signature where
  Params := Nat × Strategy
  State p := ExactRow (strategyPrefixes p.1 p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RawHistory
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ _ r => exactRowDecoder r) (fun e => nomatch e)

abbrev prefixArena : Arena where
  signature := prefixSignature
  Law R := ∀ (N : Nat) (π : Strategy) (positive : 1 ≤ N),
    Function.FactorsThrough π.policy kappa_hist → ∀ U : Source, Allowed N U →
    ∀ {e : ExactState (strategyPrefixes N π)} {h : RawHistory},
      ActualPrefix (strategyObserver N π positive) U e h →
      ∃ r : ExactRow (strategyPrefixes N π), e = .inl r ∧ r.1.1 = kappa_hist h ∧
        R.readout () (N, π) r = firstRaw h ∧ h.IsPrefix (terminal π U).1

structure ControlContext where
  G : Finset CoarseHistory
  empty : [] ∈ G
  policy : CoarseHistory → Sum Address Bool

abbrev controlSignature : Signature where
  Params := ControlContext
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Sum Address Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def controlActual : Realization controlSignature :=
  realize controlSignature (fun _ p h => historyAction (exactObserver p.empty p.policy) h)
    (fun e => nomatch e)

abbrev controlArena : Arena where
  signature := controlSignature
  Law R := ∀ {G : Finset CoarseHistory} (empty : [] ∈ G)
    (policy : CoarseHistory → Sum Address Bool),
    Function.FactorsThrough (R.readout () ⟨G, empty, policy⟩) kappa_hist

theorem count_bridge : (type_of% (@strategy_state_card)) ↔ countArena.Law countActual := Iff.rfl
theorem bound_bridge : (type_of% (@strategy_state_card_bound)) ↔ boundArena.Law countActual := Iff.rfl
theorem admissible_bridge : (type_of% (@strategy_admissible)) ↔
    admissibleArena.Law observerActual := Iff.rfl
theorem run_bridge : (type_of% (@strategy_exact_run)) ↔ runArena.Law observerActual := Iff.rfl
theorem prefix_bridge : (type_of% (@strategy_actual_prefix_replay)) ↔
    prefixArena.Law prefixActual := Iff.rfl
theorem control_bridge : (type_of% (@exact_all_history_factorization)) ↔
    controlArena.Law controlActual := Iff.rfl

theorem count_law : countArena.Law countActual := strategy_state_card
theorem bound_law : boundArena.Law countActual := strategy_state_card_bound
theorem admissible_law : admissibleArena.Law observerActual := strategy_admissible
theorem run_law : runArena.Law observerActual := strategy_exact_run
theorem prefix_law : prefixArena.Law prefixActual := strategy_actual_prefix_replay
theorem control_law : controlArena.Law controlActual := exact_all_history_factorization

theorem observer_no_dependence : ¬ ObservationalDependence observerSignature observerActual := by
  rintro h
  obtain ⟨p, x, y, different⟩ := h ()
  exact different (congrArg (observerActual.readout () p) (Subsingleton.elim x y))

#print axioms count_law
#print axioms bound_law
#print axioms admissible_law
#print axioms run_law
#print axioms prefix_law
#print axioms control_law
#print axioms count_bridge
#print axioms bound_bridge
#print axioms admissible_bridge
#print axioms run_bridge
#print axioms prefix_bridge
#print axioms control_bridge
#print axioms observer_no_dependence

abbrev membershipSignature : Signature where
  Params := Unit
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CoarseHistory
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def membershipActual : Realization membershipSignature :=
  realize membershipSignature (fun _ _ h => kappa_hist h) (fun e => nomatch e)

abbrev membershipArena : Arena where
  signature := membershipSignature
  Law R := ∀ (N : Nat) (π : Strategy) {U : Source}, Allowed N U →
    ∀ {h : RawHistory}, h.IsPrefix (terminal π U).1 →
      R.readout () () h ∈ strategyPrefixes N π

theorem membership_bridge : (type_of% (@strategy_prefix_mem)) ↔
    membershipArena.Law membershipActual := Iff.rfl

theorem membership_law : membershipArena.Law membershipActual := strategy_prefix_mem

theorem membership_dependence : ObservationalDependence membershipSignature membershipActual := by
  intro i
  exact ⟨(), [], [⟨[], Reply.absent⟩],
    by simp [membershipActual, realize, kappa_hist]⟩

#print axioms membership_bridge
#print axioms membership_law
#print axioms membership_dependence

private noncomputable def outsidePrefixes : CoarseHistory :=
  List.replicate (1 + (strategyPrefixes 1 _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.fallback).sup List.length)
    ⟨[], none⟩

noncomputable def membershipBad : Realization membershipSignature :=
  realize membershipSignature (fun _ _ _ => outsidePrefixes) (fun e => nomatch e)

theorem membership_bad : ¬ membershipArena.Law membershipBad := by
  intro law
  have member := law 1 _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.fallback (U := .of false)
    le_rfl (h := []) List.nil_prefix
  change outsidePrefixes ∈ strategyPrefixes 1 _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.fallback at member
  have bound := Finset.le_sup (f := List.length) member
  simp only [outsidePrefixes, List.length_replicate] at bound
  omega

theorem membership_variation : Variation membershipArena membershipActual :=
  ⟨membership_law, membershipBad, membership_bad⟩

theorem membership_sensitivity : Sensitivity membershipArena membershipActual := by
  constructor
  · intro i
    refine ⟨membershipBad, ?_, ?_, membership_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

noncomputable def membershipFamily : Registration membershipArena (type_of% (@strategy_prefix_mem)) where
  actual := membershipActual
  bridge := membership_bridge
  variation := membership_variation
  sensitivity := membership_sensitivity
  dependence := membership_dependence

#print axioms membershipFamily

noncomputable def membershipRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@strategy_prefix_mem) (Realization membershipSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler.membershipUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler.membershipFamily
  realizationSource := none
  generated := false
  arena := .source ⟨membershipArena⟩
  objectArena := .source ⟨membershipArena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source membershipArena ⟨membershipFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize membershipSignature membershipActual.readout membershipActual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms membershipRegistration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler
