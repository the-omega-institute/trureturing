import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionAcquisitionCut
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionAcquisitionCut

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply Strategy terminal acquisitionPolicy)
open ActualCoarseReadoutHistory (kappa_hist)
open ActualCoarseReadoutCompletion (encodeHistory compileRaw completion_contract)
open ActualJointResponseCostCore (controllerPolicy)
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound (PassiveProtocol)
open ActualFiniteObserverAbsentElimination
open Observer.ActualExactTraceCompiler
open Observer.ActualCompletionPhaseReplay
open Observer.ActualCompletionAcquisitionCut
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Parameters := Σ m : Nat, Σ _F : Fin m → Source,
  Σ _decode : CoarseHistory → Option (Fin m), PassiveProtocol Address (fun _ => Option Bool)

abbrev signature : Signature where
  Params := Parameters
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PhaseLabel p.1 × Sum Address Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ p h => routePhase p.2.1 p.2.2.1 p.2.2.2 [] (kappa_hist h))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (π : Strategy)
    (_policy : π.policy = fun h =>
      controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h))),
    (∀ (U : Source) (h : RawHistory), h.IsPrefix (terminal π U).1 →
      (R.readout () ⟨m, F, decode, p⟩ h).1 ≠ .malformed ∧
      ∀ g, (R.readout () ⟨m, F, decode, p⟩ h).1 = .acquisition g →
        ∃ v a : RawHistory, AcquisitionCut F decode p U h g v a ∧
          R.readout () ⟨m, F, decode, p⟩ h = (.acquisition g, acquisitionPolicy a) ∧
          π.policy h = acquisitionPolicy a ∧ AcquisitionGeometry U a) ∧
    (∀ (N : Nat) (positive : 1 ≤ N) (U : Source), Allowed N U →
      ∀ (e : ExactState (strategyPrefixes N π)) (h : RawHistory),
      ActualPrefix (strategyObserver N π positive) U e h →
        observerPhase F decode p N π e = (R.readout () ⟨m, F, decode, p⟩ h).1 ∧
        observerPhase F decode p N π e ≠ .malformed ∧
        ∀ g, observerPhase F decode p N π e = .acquisition g →
          ∃ v a : RawHistory, AcquisitionCut F decode p U h g v a ∧
            R.readout () ⟨m, F, decode, p⟩ h = (.acquisition g, acquisitionPolicy a) ∧
            (strategyObserver N π positive).action e = acquisitionPolicy a ∧
            AcquisitionGeometry U a ∧
            (strategyObserver N π positive).decoder e = firstRaw h ∧
            firstRaw h = a.foldl (fun cache report => cacheUpdate cache report.1 report.2)
              (firstRaw (actualRoute p U ++ v)))

theorem bridge : (type_of% (@acquisition_provenance_contract)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @acquisition_provenance_contract

private def emptyFamily : Fin 0 → Source := Fin.elim0
private def emptyDecode : CoarseHistory → Option (Fin 0) := fun _ => none

noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => (.malformed, .inr false)) (fun e => nomatch e)

theorem bad_law : ¬ arena.Law bad := by
  intro law
  obtain ⟨π, policy, _⟩ :=
    completion_contract 0 emptyFamily (fun i => Fin.elim0 i) .stop emptyDecode
  have impossible :=
    ((law emptyFamily emptyDecode .stop π policy).1 (.of true) [] List.nil_prefix).1
  exact impossible rfl

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
  cases i
  refine ⟨⟨0, emptyFamily, emptyDecode, .stop⟩, [], [⟨[], Reply.alpha⟩], ?_⟩
  intro equal
  have observed : (PhaseLabel.acquisition [] : PhaseLabel 0) =
      .acquisition [⟨[], some true⟩] := congrArg Prod.fst equal
  cases observed

noncomputable def family : Registration arena (type_of% (@acquisition_provenance_contract)) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@acquisition_provenance_contract) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionAcquisitionCut.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionAcquisitionCut.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionAcquisitionCut
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionAcquisitionCut
