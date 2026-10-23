import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeRelativePriorStability
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeRelativePriorStability
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeRelativePriorStability NativeObserverJointLaw
open NativeAcquiredPrefixState NativeFullResidual
open FourthSegmentStoppedLaw NativeConditionalControl.DepthLaw NativeConditionalControl.Tail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open MeasureTheory ProbabilityTheory
open scoped ENNReal

abbrev tailSignature : Signature where
  Params := PMF Depth × PMF Depth × ℝ × ActivePhase
  State _ := List Operation × AcquiredNativeState
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Measure (ValidTail p.2.2.2)
  Anchor := Empty
  finiteAnchor := inferInstance

def tailActual : Realization tailSignature := realize _
  (fun i p z => rawTarget (if i = 0 then p.1 else p.2.1) z.1 z.2 p.2.2.2)
  (fun e => nomatch e)

def tailArena : Arena where
  signature := tailSignature
  Law R := ∀ (μ ν : PMF Depth) (ζ : ℝ), 0 ≤ ζ → ζ < 1 →
    (∀ k, ENNReal.ofReal (1 - ζ) * μ k ≤ ν k ∧
      ν k ≤ ENNReal.ofReal (1 + ζ) * μ k) →
    ∀ (h : List Operation) (c : AcquiredNativeState), run h = some c →
    ∀ s : ActivePhase,
      measurableTotalVariation (R.readout 0 (μ, ν, ζ, s) (h, c))
        (R.readout 1 (μ, ν, ζ, s) (h, c)) ≤ ENNReal.ofReal (ζ / (1 - ζ))

theorem native_relative_prior_tail_bridge : (type_of% (@native_relative_prior_tail)) ↔
    tailArena.Law tailActual := Iff.rfl

theorem native_relative_prior_tail_actual_law : tailArena.Law tailActual :=
  native_relative_prior_tail_bridge.mp native_relative_prior_tail

#print axioms native_relative_prior_tail_actual_law
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeRelativePriorStability
