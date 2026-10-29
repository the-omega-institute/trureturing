import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeTwoMomentRecovery
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeTwoMomentRecovery

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeConditionalControl.DepthLaw NativeObserverJointLaw FourthSegmentStoppedLaw
open NativeTwoMomentRecovery NativePaidHistoryCommonRow
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit ProbabilityTheory
open scoped ENNReal BigOperators

abbrev signature : Signature where
  Params := Σ s : ActivePhase, PhaseHistory s
  State _ := PMF Depth
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := PMF Depth
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p μ => posterior μ p.2.val.1 p.2.val.2 p.2.property.1)
    (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => PMF.pure 1) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ (μ : PMF Depth) (s t : ActivePhase) (H : PhaseHistory s) (G : PhaseHistory t),
    (∑' k, (posterior μ H.val.1 H.val.2 H.property.1 k).toReal * (rate k : ℝ)) =
      (∑' k, (posterior μ G.val.1 G.val.2 G.property.1 k).toReal * (rate k : ℝ)) →
    (∑' k, (posterior μ H.val.1 H.val.2 H.property.1 k).toReal * (rate k : ℝ) ^ 2) =
      (∑' k, (posterior μ G.val.1 G.val.2 G.property.1 k).toReal * (rate k : ℝ) ^ 2) →
    R.readout () ⟨s, H⟩ μ = posterior μ G.val.1 G.val.2 G.property.1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro T
  let H := windowPhaseHistory 0 0 0 .p
  have h := T (PMF.pure 2) .p .p H H rfl rfl
  have he := congrArg (fun ν : PMF Depth => (ν 1).toReal) h
  change (PMF.pure (1:Depth) 1).toReal =
    (posterior (PMF.pure 2) H.val.1 H.val.2 H.property.1 1).toReal at he
  have hp := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow.posterior_pure_readout
    2 1 .p H
  change (posterior (PMF.pure 2) H.val.1 H.val.2 H.property.1 1).toReal = _ at hp
  norm_num at hp
  rw [hp] at he
  norm_num [PMF.pure_apply] at he

def record : Registration arena (type_of% (@same_prior_two_moments_posterior_unique)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨same_prior_two_moments_posterior_unique, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    cases i
    let H := windowPhaseHistory 0 0 0 .p
    refine ⟨⟨.p, H⟩, PMF.pure 1, PMF.pure 2, ?_⟩
    intro he
    have hx := congrArg (fun ν : PMF Depth => (ν 1).toReal) he
    change (posterior (PMF.pure 1) H.val.1 H.val.2 H.property.1 1).toReal =
      (posterior (PMF.pure 2) H.val.1 H.val.2 H.property.1 1).toReal at hx
    have hp := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow.posterior_pure_readout
      1 1 .p H
    have hq := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow.posterior_pure_readout
      2 1 .p H
    change (posterior (PMF.pure 1) H.val.1 H.val.2 H.property.1 1).toReal = _ at hp
    change (posterior (PMF.pure 2) H.val.1 H.val.2 H.property.1 1).toReal = _ at hq
    norm_num at hp hq
    rw [hp, hq] at hx
    exact (zero_ne_one hx.symm)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@same_prior_two_moments_posterior_unique)
    (type_of% (realize signature
      (fun _ p μ => posterior μ p.2.val.1 p.2.val.2 p.2.property.1)
      (fun a => nomatch a))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeTwoMomentRecovery.posterior,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeTwoMomentRecovery.record,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p μ => posterior μ p.2.val.1 p.2.val.2 p.2.property.1)
    (fun a => nomatch a)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeTwoMomentRecovery,
    definition := none,
    coordinates := #[1, 3],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn","fn","fn","arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeTwoMomentRecovery
