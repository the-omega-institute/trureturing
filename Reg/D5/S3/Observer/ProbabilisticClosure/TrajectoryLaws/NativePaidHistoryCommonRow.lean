import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw NativeConditionalControl.Prefix
open NativeObserverJointLaw NativeInstalledFullLaw NativeFullResidual NativePaidHistoryCommonRow
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u
abbrev Complete := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.Complete
abbrev base := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.liftedBase
abbrev emitter := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.baseEmitter

abbrev signature : Signature where
  Params := Complete.{u}
  State _ := List Operation × Depth
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ h => likelihood h.1 h.2) (fun a => nomatch a)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ (C : Complete.{u}) (e : InstalledEmitter C.observer) (μ : PMF Depth) (m t j : ℕ) (s : ActivePhase),
    let H := windowPhaseHistory m t j s
    (run H.val.1 = some H.val.2) ∧
    H.val.2.source.finiteFields = ⟨.fourth (.active s), heldRegisters⟩ ∧
    H.val.2.counts = ⟨2*m+3+j, 2*t+3+j + match s with | .p => 0 | .beta => 1⟩ ∧
    (∀ k : Depth, 0 < R.readout () C (H.val.1,k) ∧
      R.readout () C (H.val.1,k) = alphaMass (rate k)^(2*m+3+j) *
        betaMass (rate k)^(2*t+3+j + match s with | .p => 0 | .beta => 1)) ∧
    (0 < normalizer μ H.val.1 ∧ normalizer μ H.val.1 ≤ 1) ∧
    (∀ z ∈ (row C.observer H.val.1).support,
      C.observer.project z = ⟨.fourth (.active s), heldRegisters⟩ ∧
      fullLaw C.observer e z = (tailLaw C.observer e s z).map (fullRenderer H.val.2 s)) ∧
    (∑ z, row C.observer H.val.1 z * measurableTotalVariation (tailLaw C.observer e s z)
      (rawTarget μ H.val.1 H.val.2 s)) ≤ installedRisk C.observer e μ s ∧
    measurableTotalVariation (tailMixture C.observer e s (row C.observer H.val.1))
      (rawTarget μ H.val.1 H.val.2 s) ≤ installedLawRisk C.observer e μ s ∧
    rawLawRisk C.observer e μ s = installedLawRisk C.observer e μ s ∧
    installedLawRisk C.observer e μ s ≤ installedRisk C.observer e μ s ∧
    (∀ k i : Depth, 0 < m → 0 < t →
      Real.log ((R.readout () C (H.val.1,i)).toReal / (R.readout () C (H.val.1,k)).toReal) ≤
        2*((m:ℝ)-(rate k:ℝ)*(m+t))^2/((m+t)*(rate k:ℝ)*(1-(rate k:ℝ))) +
          suffixLogRatio j s k i) ∧
    (∀ k i : Depth, i ≠ k →
      (rate k:ℝ)*Real.log ((rate i:ℝ)/(rate k:ℝ)) +
        (1-(rate k:ℝ))*Real.log ((1-(rate i:ℝ))/(1-(rate k:ℝ))) < 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro T
  have h := (T base emitter (PMF.pure 1) 0 0 0 .p).2.2.2.1 1
  exact (lt_irrefl (0:ℝ≥0∞)) h.1

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨base, ([],1), ([.read 0],1), ?_⟩
  intro h
  have hr := congrArg ENNReal.toReal h
  norm_num [actual, realize, likelihood, readLetters, wordMass, rate,
    alphaMass, unitInterval.toNNReal, ENNReal.coe_toReal, Nat.fib] at hr
  change (1:ℝ) = 1/3 at hr
  norm_num at hr

def record : Registration arena.{u} (type_of% (@native_paid_window_control.{u})) where
  actual := actual
  bridge := by
    constructor
    · intro T C e μ m t j s
      exact T C.observer e μ m t j s
    · intro T Z finite measurable singleton M e μ m t j s
      exact T ⟨Z,finite,measurable,singleton,M⟩ e μ m t j s
  variation := ⟨(fun C e μ m t j s => native_paid_window_control C.observer e μ m t j s),
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro a; exact nomatch a
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_paid_window_control.{u})
    (type_of% (realize signature.{u} (fun _ _ h => likelihood h.1 h.2)
      (fun a => nomatch a))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow.window,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ _ h => likelihood h.1 h.2)
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
open Filter Topology

abbrev posteriorSignature : Signature where
  Params := PMF Depth
  State _ := Depth × (Σ s : ActivePhase, PhaseHistory s)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def posteriorActual : Realization posteriorSignature :=
  realize posteriorSignature (fun _ μ q =>
    (posterior μ q.2.2.val.1 q.2.2.val.2 q.2.2.property.1 q.1).toReal)
    (fun a => nomatch a)
def posteriorRejected : Realization posteriorSignature :=
  realize posteriorSignature (fun _ _ _ => 0) (fun a => nomatch a)

def posteriorArena : Arena where
  signature := posteriorSignature
  Law R := ∀ (μ : PMF Depth) (k : Depth), μ k ≠ 0 → ∀ (j : ℕ) (s : ActivePhase),
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop, 2 ≤ w ∧
      ∀ u v : ℕ, u < w → v < w →
        let H := windowPhaseHistory (windowCount w (rate k) u)
          (windowCount w (1-(rate k:ℝ)) v) j s
        1-R.readout () μ (k,⟨s,H⟩) < ε

private theorem posterior_rejected_law : ¬ posteriorArena.Law posteriorRejected := by
  intro h
  have ht := h (PMF.pure 1) 1 (by simp) 0 .p (1/2) (by norm_num)
  obtain ⟨w,hw,hb⟩ := ht.exists
  have he := hb 0 0 (by omega) (by omega)
  norm_num [posteriorRejected, realize] at he

private theorem posterior_pure_readout (l k : Depth) (s : ActivePhase) (H : PhaseHistory s) :
    posteriorActual.readout () (PMF.pure l) (k,⟨s,H⟩) = if k = l then 1 else 0 := by
  have hL := likelihood_pos H.val.1 l
  have hLf : likelihood H.val.1 l ≠ ∞ := by
    rw [likelihood, word_counts]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp [alphaMass]))
      (ENNReal.pow_ne_top (by simp [betaMass]))
  simp only [posteriorActual, realize, posterior, PMF.normalize_apply]
  change ((PMF.pure l k * likelihood H.val.1 k) * (normalizer (PMF.pure l) H.val.1)⁻¹).toReal = _
  have hN : normalizer (PMF.pure l) H.val.1 = likelihood H.val.1 l := by
    simp [normalizer, PMF.pure_apply, tsum_ite_eq, eq_comm]
  rw [hN]
  by_cases hk : k = l
  · subst k
    simp [PMF.pure_apply, ENNReal.mul_inv_cancel hL.ne' hLf]
  · simp [PMF.pure_apply, hk]

private theorem posterior_dependence : ObservationalDependence posteriorSignature posteriorActual := by
  intro r
  cases r
  refine ⟨PMF.pure 1, (1,⟨.p,windowPhaseHistory 0 0 0 .p⟩),
    (2,⟨.p,windowPhaseHistory 0 0 0 .p⟩), ?_⟩
  rw [posterior_pure_readout, posterior_pure_readout]
  norm_num

def posteriorRecord : Registration posteriorArena
    (type_of% native_countable_posterior_concentration) where
  actual := posteriorActual
  bridge := by
    constructor
    · intro T μ k hk j s ε hε
      exact T μ k hk j s ε hε
    · intro T μ k hk j s ε hε
      exact T μ k hk j s ε hε
  variation := ⟨native_countable_posterior_concentration,
    posteriorRejected, posterior_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨posteriorRejected, ?_, rfl, posterior_rejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro a; exact nomatch a
  dependence := posterior_dependence

def posteriorRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    native_countable_posterior_concentration
    (type_of% (realize posteriorSignature (fun _ μ q =>
      (posterior μ q.2.2.val.1 q.2.2.val.2 q.2.2.property.1 q.1).toReal)
      (fun a => nomatch a))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow.posterior,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow.posteriorRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨posteriorArena⟩, objectArena := .source ⟨posteriorArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source posteriorArena ⟨posteriorRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize posteriorSignature (fun _ μ q =>
    (posterior μ q.2.2.val.1 q.2.2.val.2 q.2.2.property.1 q.1).toReal)
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

#print axioms posteriorRecord
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow
