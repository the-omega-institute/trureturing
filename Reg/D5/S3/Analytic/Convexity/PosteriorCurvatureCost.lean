import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Convexity.PosteriorCurvatureCost
import Reg.Support.DependentFamily

/-! Faithful weak finite-measure source operands. These compiled source bridges
supply no serialization or source-identity-bytes certificate. -/

open Set MeasureTheory LeanInformationAudit
open scoped ENNReal NNReal Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Convexity.PosteriorCurvatureCost

noncomputable section
namespace Reg.D5.S3.Analytic.Convexity.PosteriorCurvatureCost

structure Inputs where
  f : ℝ → ℝ
  convex : ConvexOn ℝ (Ioi 0) f

abbrev signature : Signature where
  Params := Inputs
  State _ := FiniteMeasure Posterior
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a ν => posteriorCurvatureCost a.convex ν) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : Inputs, LowerSemicontinuous (R.readout () a)

/-- The entire weak topology and all convex functions remain in the source bridge. -/
theorem source_bridge :
    (type_of% (@posteriorCurvatureCost_lowerSemicontinuous)) ↔ arena.Law actual := by
  constructor
  · intro h a
    exact h a.convex
  · intro h f hf
    exact h ⟨f, hf⟩

abbrev truncationArena : Arena where
  signature := signature
  Law R := ∀ (a : Inputs) (ν : FiniteMeasure Posterior),
    R.readout () a ν = ⨆ n, ∫⁻ t, (posteriorTruncation a.convex n t : ℝ≥0∞) ∂ν

theorem truncation_source_bridge :
    (type_of% (@posteriorCurvatureCost_eq_iSup)) ↔ truncationArena.Law actual := by
  constructor
  · intro h a ν
    exact h a.convex ν
  · intro h f hf ν
    exact h ⟨f, hf⟩ ν


theorem nonnegative_source_bridge : (type_of% (@curvatureTruncation_nonneg)) ↔
    ∀ {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (n : ℕ) (u v : ℝ),
      0 ≤ curvatureTruncation hf n u v := Iff.rfl

theorem continuous_source_bridge : (type_of% (@curvatureTruncation_continuous)) ↔
    ∀ {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (n : ℕ),
      Continuous (fun z : ℝ × ℝ => curvatureTruncation hf n z.1 z.2) := Iff.rfl

theorem monotone_source_bridge : (type_of% (@curvatureTruncation_monotone)) ↔
    ∀ {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (u v : ℝ),
      Monotone (fun n => curvatureTruncation hf n u v) := Iff.rfl

theorem exhaustion_source_bridge : (type_of% (@iSup_curvatureTruncation)) ↔
    ∀ {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (u v : ℝ),
      (⨆ n, ENNReal.ofReal (curvatureTruncation hf n u v)) =
        _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation.curvatureRemainder hf u v :=
  Iff.rfl

#print axioms source_bridge
#print axioms truncation_source_bridge

end Reg.D5.S3.Analytic.Convexity.PosteriorCurvatureCost
