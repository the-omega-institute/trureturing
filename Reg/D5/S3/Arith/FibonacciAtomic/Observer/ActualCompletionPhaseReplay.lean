import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply Strategy leaves acquisitionPolicy)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualCoarseReadoutCompletion (encodeHistory compileRaw completion_contract)
open ActualJointResponseCostCore (controllerPolicy)
open ActualImageSevenLeafSeparation (leafLabel)
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open Observer.ActualExactTraceCompiler
open Observer.ActualCompletionPhaseReplay
open ActualFiniteObserverAbsentElimination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Parameters := Σ m : Nat, Σ _F : Fin m → Source,
  Σ _decode : CoarseHistory → Option (Fin m), PassiveProtocol Address (fun _ => Option Bool)

abbrev signature : Signature where
  Params := Parameters
  State _ := CoarseHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Sum Address Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ p g => (routePhase p.2.1 p.2.2.1 p.2.2.2 [] g).2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (positive : 1 ≤ N)
    (policy : π.policy = fun h =>
      controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h))),
    (∀ g, R.readout () ⟨m, F, decode, p⟩ g =
      controllerPolicy (compileRaw F decode p []) (encodeHistory g)) ∧
    (∀ U s, routePhase F decode p []
        (runPassiveProtocol (fun q W => leafLabel W q) p U ++ s) =
      routePhase F decode .stop
        (runPassiveProtocol (fun q W => leafLabel W q) p U) s) ∧
    (∀ (i : Fin m) (pre rest : List Address) (q : Address) (y : Reply) (s : CoarseHistory),
      leaves (F i) = pre ++ q :: rest → kappa y ≠ leafLabel (F i) q →
      verifyPhase F i (leaves (F i)) []
          (pre.map (fun a => ⟨a, leafLabel (F i) a⟩) ++ [⟨q, kappa y⟩] ++ s) =
        (.acquisition s, acquisitionPolicy (encodeHistory s))) ∧
    (∀ seen g phaseHistory,
      (routePhase F decode p seen g).1 = .route phaseHistory → phaseHistory = seen ++ g) ∧
    (∀ (i j : Fin m) (qs rest : List Address) (seen g phaseHistory : CoarseHistory),
      (verifyPhase F i qs seen g).1 = .verify j rest phaseHistory →
      j = i ∧ ∃ used leftover : CoarseHistory,
        g = used ++ leftover ∧ qs = used.map Sigma.fst ++ rest ∧
        phaseHistory = seen ++ used ∧ (rest ≠ [] → leftover = []) ∧
        ∀ a ∈ used, a.2 = leafLabel (F i) a.1) ∧
    (∀ U, Allowed N U → ∀ e h,
      ActualPrefix (strategyObserver N π positive) U e h →
        observerPhase F decode p N π e = (routePhase F decode p [] (kappa_hist h)).1 ∧
        observerPhase F decode p N π e ∈ phaseAlphabet F decode p N π ∧
        (routePhase F decode p [] (kappa_hist h)).2 = π.policy h)

theorem bridge : (type_of% (@phase_replay_contract)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @phase_replay_contract

private def emptyFamily : Fin 0 → Source := Fin.elim0
private def emptyDecode : CoarseHistory → Option (Fin 0) := fun _ => none
private def testRoute : PassiveProtocol Address (fun _ => Option Bool) :=
  .query [true] (fun _ => .stop)

noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => .inr false) (fun e => nomatch e)

theorem bad_law : ¬ arena.Law bad := by
  intro law
  obtain ⟨π, policy, _⟩ := completion_contract 0 emptyFamily (fun i => Fin.elim0 i)
    testRoute emptyDecode
  have impossible := (law emptyFamily emptyDecode testRoute 1 π le_rfl policy).1 []
  change (Sum.inr false : Sum Address Bool) = .inl [true] at impossible
  cases impossible

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
  refine ⟨⟨0, emptyFamily, emptyDecode, testRoute⟩, [], [⟨[true], none⟩], ?_⟩
  change (Sum.inl [true] : Sum Address Bool) ≠ .inl []
  decide

noncomputable def family : Registration arena (type_of% (@phase_replay_contract)) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@phase_replay_contract) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay
    definition := none
    coordinates := #[0, 1, 2, 3]
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

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay
