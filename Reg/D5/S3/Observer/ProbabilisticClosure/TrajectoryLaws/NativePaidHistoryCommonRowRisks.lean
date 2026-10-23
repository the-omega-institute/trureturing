import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw NativeConditionalControl.Prefix
open NativeObserverJointLaw NativeInstalledFullLaw NativeFullResidual NativePaidHistoryCommonRow
open NativePaidHistoryCommonRowLimits NativePaidHistoryCommonRowRisks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u
abbrev Complete := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.Complete
abbrev base := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.liftedBase
abbrev emitter := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.baseEmitter
abbrev signature : Signature where
  Params := Complete.{u}
  State C := Operation × C.Z × C.Z
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ C q => C.observer.update q.1 q.2.1 q.2.2) (fun a => nomatch a)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ (C : Complete.{u}) (e : InstalledEmitter C.observer) (μ : PMF Depth),
    ∃ pi tau : PMF C.Z,
      (∀ y : C.Z, (∑ x, pi x*R.readout () C (.read 1,x,y)) = tau y) ∧
      (∀ x : C.Z, (∑ y, tau y*R.readout () C (.read 0,y,x)) = pi x) ∧
      (∀ k : Depth, μ k ≠ 0 → ∀ s : ActivePhase,
        (∑ z, phaseRow pi tau s z*D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction.measurableTotalVariation
          (tailLaw C.observer e s z) (pureTail k s)) ≤ installedRisk C.observer e μ s ∧
        D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction.measurableTotalVariation
          (tailMixture C.observer e s (phaseRow pi tau s)) (pureTail k s) ≤ installedLawRisk C.observer e μ s) ∧
      (∀ s : ActivePhase, ∀ z ∈ (phaseRow pi tau s).support, ∃ m t j : ℕ,
        0 < row C.observer (windowHistory m t j s) z ∧
        0 < normalizer μ (windowHistory m t j s) ∧
        C.observer.project z = heldFields s ∧
        fullLaw C.observer e z = (tailLaw C.observer e s z).map (fullRenderer (windowState m t j s) s)) ∧
      (∀ x ∈ pi.support, ∀ y ∈ (C.observer.update (.read 1) x).support, y ∈ tau.support) ∧
      (∀ y ∈ tau.support, ∀ x ∈ (C.observer.update (.read 0) y).support, x ∈ pi.support) ∧
      (∃ q : C.Z → C.Z, ∃ hq : ∀ z, C.observer.project (q z) = C.observer.project z,
        (∀ z, retained C.observer pi tau (q z)) ∧
        (∀ z, retained C.observer pi tau z → q z = z) ∧
        (∀ op z y, y ∈ ((clippedObserver C.observer q hq).update op z).support → retained C.observer pi tau y) ∧
        (∀ x ∈ pi.support, (clippedObserver C.observer q hq).update (.read 1) x = C.observer.update (.read 1) x) ∧
        (∀ y ∈ tau.support, (clippedObserver C.observer q hq).update (.read 0) y = C.observer.update (.read 0) y) ∧
        (∀ z, z ∈ pi.support ∨ z ∈ tau.support →
          markedLaw (clippedObserver C.observer q hq) (clippedEmitter C.observer e q hq) (z,none) = markedLaw C.observer e (z,none) ∧
          fullLaw (clippedObserver C.observer q hq) (clippedEmitter C.observer e q hq) z = fullLaw C.observer e z ∧
          ∀ s : ActivePhase, tailLaw (clippedObserver C.observer q hq) (clippedEmitter C.observer e q hq) s z = tailLaw C.observer e s z))

private theorem source_to_law (T : type_of% (@native_complete_common_rows.{u})) : arena.{u}.Law actual.{u} := by
  intro C e μ
  obtain ⟨pi,tau,hB,hA,rest⟩ := T C.observer e μ
  refine ⟨pi,tau,?_,?_,rest⟩
  · intro y
    have h := congrArg (fun η : PMF C.Z => η y) hB
    simpa only [PMF.bind_apply, tsum_fintype, actual, realize] using h
  · intro x
    have h := congrArg (fun η : PMF C.Z => η x) hA
    simpa only [PMF.bind_apply, tsum_fintype, actual, realize] using h

private theorem law_to_source (T : arena.{u}.Law actual.{u}) : type_of% (@native_complete_common_rows.{u}) := by
  intro Z finite measurable singleton M e μ
  let C : Complete.{u} := ⟨Z,finite,measurable,singleton,M⟩
  obtain ⟨pi,tau,hB,hA,rest⟩ := T C e μ
  refine ⟨pi,tau,?_,?_,rest⟩
  · ext y
    simpa only [PMF.bind_apply, tsum_fintype, actual, realize] using hB y
  · ext x
    simpa only [PMF.bind_apply, tsum_fintype, actual, realize] using hA x

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro T
  obtain ⟨pi,tau,hB,rest⟩ := T base emitter (PMF.pure 1)
  have hz : ∀ y, tau y = 0 := by
    intro y
    have h := hB y
    simpa only [rejected, realize, mul_zero, Finset.sum_const_zero] using h.symm
  have hm := tau.tsum_coe
  simp only [hz, tsum_zero] at hm
  exact zero_ne_one hm

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  let f : FiniteFields := {initial.source.finiteFields with control := .seed (some 0)}
  refine ⟨base, (.read 0, ULift.up initial.source.finiteFields, ULift.up f),
    (.read 0, ULift.up initial.source.finiteFields, ULift.up initial.source.finiteFields), ?_⟩
  intro h
  change ((PMF.pure f).map ULift.up) (ULift.up f) =
    ((PMF.pure f).map ULift.up) (ULift.up initial.source.finiteFields) at h
  rw [PMF.pure_map] at h
  simp [PMF.pure_apply, f, initial] at h

def record : Registration arena.{u} (type_of% (@native_complete_common_rows.{u})) where
  actual := actual
  bridge := ⟨source_to_law,law_to_source⟩
  variation := ⟨source_to_law (@native_complete_common_rows.{u}),rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro a; exact nomatch a
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_complete_common_rows.{u})
    (type_of% (realize signature.{u} (fun _ C q => C.observer.update q.1 q.2.1 q.2.2)
      (fun a => nomatch a))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks.common,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ C q => C.observer.update q.1 q.2.1 q.2.2)
    (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none, sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms record
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks
