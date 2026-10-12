import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply Strategy terminal)
open ActualCoarseReadoutHistory (kappa_hist)
open ActualCoarseReadoutCompletion (compileRaw encodeHistory completion_contract)
open ActualJointResponseCostCore (controllerPolicy controllerOutcome)
open ActualFiniteObserverAbsentElimination (Allowed RawHistory)
open Observer.ActualObserverAbsorbingNormalization (allowedSources)
open Observer.ActualExactTraceCompiler (ExactState strategyPrefixes)
open Observer.ActualCompletionHorizon
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Parameters := Σ m : Nat, Σ _F : Fin m → Source,
  Σ _decode : CoarseHistory → Option (Fin m),
  Σ _p : PassiveProtocol Address (fun _ => Option Bool), Σ _N : Nat, Strategy

abbrev signature : Signature where
  Params := Parameters
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RawHistory × Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ p U => terminal p.2.2.2.2.2 U) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (positive : 1 ≤ N)
    (policy : π.policy = fun h => controllerPolicy (compileRaw F decode p [])
      (encodeHistory (kappa_hist h))),
    (∀ U : Source, R.readout () ⟨m, F, decode, p, N, π⟩ U =
      controllerOutcome (compileRaw F decode p []) U) ∧
    (∀ U : Source, Allowed N U →
      (terminal π U).1.length ≤ routeHorizon p + prototypeMax F + (2 * N - 1) ∧
      (∀ a ∈ (terminal π U).1,
        a.1 ∈ qNFinset N ∪ routeSupport p ∪ prototypeLeaves F)) ∧
    Fintype.card (ExactState (strategyPrefixes N π)) ≤
      1 + (allowedSources N).card *
        (routeHorizon p + prototypeMax F + (2 * N - 1) + 1) *
        2 ^ min (qNFinset N ∪ routeSupport p ∪ prototypeLeaves F).card
          (routeHorizon p + prototypeMax F + (2 * N - 1))

theorem bridge : (type_of% (@actual_completion_horizon)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @actual_completion_horizon

private def emptyFamily : Fin 0 → Source := Fin.elim0
private def emptyDecode : CoarseHistory → Option (Fin 0) := fun _ => none

noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => ([], false)) (fun e => nomatch e)

theorem bad_law : ¬ arena.Law bad := by
  intro law
  obtain ⟨π, policy, _⟩ := completion_contract 0 emptyFamily (fun i => Fin.elim0 i)
    .stop emptyDecode
  have impossible := (law emptyFamily emptyDecode .stop 1 π le_rfl policy).1 (.of true)
  have emptyEq := congrArg (fun z : RawHistory × Bool => z.1.length) impossible
  change 0 = 1 at emptyEq
  omega

theorem variation : Variation arena actual := ⟨actual_law, bad, bad_law⟩

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, bad_law⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨π, policy, _⟩ := completion_contract 0 emptyFamily (fun j => Fin.elim0 j)
    .stop emptyDecode
  refine ⟨⟨0, emptyFamily, emptyDecode, .stop, 1, π⟩, .of true, .of false, ?_⟩
  have exactOutcome := (actual_completion_horizon emptyFamily emptyDecode .stop 1 π
    le_rfl policy).1
  change terminal π (.of true) ≠ terminal π (.of false)
  rw [exactOutcome, exactOutcome]
  intro equal
  have traceEq := congrArg (fun z : RawHistory × Bool => z.1.map Sigma.snd) equal
  change [Reply.alpha] = [Reply.beta] at traceEq
  cases traceEq

noncomputable def family : Registration arena (type_of% (@actual_completion_horizon)) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@actual_completion_horizon) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon
