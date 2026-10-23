import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionCounterfactualEscape
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionCounterfactualEscape

universe u

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply Strategy acquisitionPolicy fallback)
open ActualCoarseReadoutHistory (kappa_hist)
open ActualCoarseReadoutCompletion (encodeHistory compileRaw completion_contract)
open ActualJointResponseCostCore (controllerPolicy)
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound (PassiveProtocol)
open Observer.ActualExactTraceCompiler (CoarseHistory)
open Observer.ActualCompletionPhaseReplay (PhaseLabel routePhase)
open Observer.ActualCompletionCounterfactualEscape
open ActualFiniteObserverAbsentElimination (RawHistory Observer historyAction)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Strategy
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Sum Address Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ π h => π.policy h) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (π : Strategy)
    (policy : π.policy = fun h =>
      controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h))),
    ∃ pre : RawHistory,
      (∀ k : Fin pre.length, π.policy (pre.take k.val) = Sum.inl ((pre.get k).1)) ∧
      (∀ s : RawHistory, routePhase F decode p [] (kappa_hist (pre ++ s)) =
        (PhaseLabel.acquisition (kappa_hist s), acquisitionPolicy (encodeHistory (kappa_hist s)))) ∧
      (∀ n : Nat, R.readout () π (pre ++ branchHistory n) = Sum.inl (leftAddress n)) ∧
      (∀ (E : Type u) [Fintype E] (M : Observer E), ∃ n : Nat,
        historyAction M (pre ++ branchHistory n) ≠ π.policy (pre ++ branchHistory n))

theorem bridge : (type_of% (@counterfactual_escape.{u})) ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_law : arena.{u}.Law actual := @counterfactual_escape.{u}

private def emptyFamily : Fin 0 → Source := Fin.elim0
private def emptyDecode : CoarseHistory → Option (Fin 0) := fun _ => none

noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => .inr false) (fun e => nomatch e)

theorem bad_law : ¬ arena.{u}.Law bad := by
  intro law
  obtain ⟨π, policy, _⟩ := completion_contract 0 emptyFamily (fun i => Fin.elim0 i)
    .stop emptyDecode
  obtain ⟨pre, _, _, ladder, _⟩ := law emptyFamily emptyDecode .stop π policy
  have impossible := ladder 0
  change (Sum.inr false : Sum Address Bool) = Sum.inl (leftAddress 0) at impossible
  cases impossible

theorem variation : Variation arena.{u} actual := ⟨actual_law, bad, bad_law⟩

theorem sensitivity : Sensitivity arena.{u} actual := by
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
  refine ⟨fallback, [], branchHistory 1, ?_⟩
  change (Sum.inl [] : Sum Address Bool) ≠ Sum.inl [false]
  decide

noncomputable def family : Registration arena.{u} (type_of% (@counterfactual_escape.{u})) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counterfactual_escape.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionCounterfactualEscape.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionCounterfactualEscape.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionCounterfactualEscape
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms counterfactual_escape
#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionCounterfactualEscape
