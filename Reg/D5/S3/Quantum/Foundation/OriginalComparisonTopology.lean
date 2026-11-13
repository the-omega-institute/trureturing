import D5.S3.Quantum.Foundation.OriginalComparisonTopology
import Reg.D5.S3.Quantum.Foundation.OriginalBallScale

/-! Exact original telescopes and actual-positive source reconstruction.
The scoped observation is original pure reciprocity. Whole-family variation,
sensitivity and observational dependence are unfinished; these arenas are not
validated four-slot registrations. -/
noncomputable section
universe v
open Set Filter Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace Reg.D5.S3.Quantum.Foundation.OriginalComparisonTopology
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OriginalFacePolarity
open _root_.D5.S3.Quantum.Foundation.OriginalBallScale
open _root_.D5.S3.Quantum.Foundation.OriginalComparisonTopology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight
open Reg.D5.S3.Quantum.Foundation.OriginalBallScale

abbrev arena0 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) ,
    ∃ L : ℝ, 0 < L ∧ ∀ p : pure P.cone P.unit, ∀ x ∈ base P.cone P.unit, ∀ y ∈ base P.cone P.unit,
      |comparison P.cone P.unit p x - comparison P.cone P.unit p y| ≤ L * ‖x - y‖

abbrev source0 : Prop := type_of% (@original_uniform_comparison.{v})

theorem source_bridge_0 : source0.{v} ↔ arena0.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_0 : arena0.{v}.Law actual.{v} :=
  source_bridge_0.mp (@original_uniform_comparison.{v})

abbrev arena1 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hc : IsClosed (P.cone : Set P.V)) (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) (hB : exclusionBalls P.cone P.unit)
    (hPR : ∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p)) ,
    ∃ L : ℝ, 0 < L ∧ ∀ (p : pure P.cone P.unit) (a : ExclusionChart P.cone P.unit p),
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
        (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → extensionBudget a v = 1 / (2*t)) ∧
        ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 →
          2*t ≤ L * ‖a.param v - a.param (-v)‖

abbrev source1 : Prop := type_of% (@original_scale_axis_bound.{v})

theorem source_bridge_1 : source1.{v} ↔ arena1.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_1 : arena1.{v}.Law actual.{v} :=
  source_bridge_1.mp (@original_scale_axis_bound.{v})

abbrev arena2 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hc : IsClosed (P.cone : Set P.V)) (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) (hB : exclusionBalls P.cone P.unit)
    (hPR : ∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p))
    (U : Set (pure P.cone P.unit)) (B : ℝ) (hBpos : 0 < B)
    (hbudget : ∀ p ∈ U, ∀ a : ExclusionChart P.cone P.unit p,
      ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → extensionBudget a v ≤ B) ,
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ U, δ ≤ Metric.diam (exclusion P.cone P.unit p)

abbrev source2 : Prop := type_of% (@original_bounded_budget_noncollapse.{v})

theorem source_bridge_2 : source2.{v} ↔ arena2.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_2 : arena2.{v}.Law actual.{v} :=
  source_bridge_2.mp (@original_bounded_budget_noncollapse.{v})

abbrev arena3 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hc : IsClosed (P.cone : Set P.V)) (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) (hB : exclusionBalls P.cone P.unit)
    (hPR : ∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p))
    (pn : ℕ → pure P.cone P.unit) (a : ∀ n, ExclusionChart P.cone P.unit (pn n))
    (v : ∀ n, EuclideanSpace ℝ (Fin (a n).dim)) (hv : ∀ n, ‖v n‖ = 1)
    (hd : Tendsto (fun n => Metric.diam (exclusion P.cone P.unit (pn n))) atTop (𝓝 0)) ,
    Tendsto (fun n => extensionBudget (a n) (v n)) atTop atTop

abbrev source3 : Prop := type_of% (@original_diameter_collapse_budget.{v})

theorem source_bridge_3 : source3.{v} ↔ arena3.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_3 : arena3.{v}.Law actual.{v} :=
  source_bridge_3.mp (@original_diameter_collapse_budget.{v})

abbrev arena4 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hc : IsClosed (P.cone : Set P.V)) (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) (hB : exclusionBalls P.cone P.unit)
    (hPR : ∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p))
    (U : Set (pure P.cone P.unit)) (δ : ℝ) (hδ : 0 < δ)
    (hdiam : ∀ p ∈ U, δ ≤ Metric.diam (exclusion P.cone P.unit p)) ,
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ U, ∀ a : ExclusionChart P.cone P.unit p,
      ∀ w : EuclideanSpace ℝ (Fin a.dim), ‖w‖ = 1 → extensionBudget a w ≤ B

abbrev source4 : Prop := type_of% (@original_noncollapse_bounded_budget.{v})

theorem source_bridge_4 : source4.{v} ↔ arena4.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_4 : arena4.{v}.Law actual.{v} :=
  source_bridge_4.mp (@original_noncollapse_bounded_budget.{v})

abbrev arena5 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hc : IsClosed (P.cone : Set P.V)) (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (h3 : _root_.D5.S3.Quantum.Foundation.ReciprocalExclusionLimits.threeBallExclusions P.cone P.unit)
    (hPR : ∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p))
    (p : pure P.cone P.unit) ,
    ContinuousAt (_root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.wholeExclusion hc hs hg (_root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.ballHyp h3)) p ↔
      ∃ U : Set (pure P.cone P.unit), IsOpen U ∧ p ∈ U ∧ ∃ B : ℝ, 0 < B ∧
        ∀ s ∈ U, ∀ a : ExclusionChart P.cone P.unit s,
          ∀ w : EuclideanSpace ℝ (Fin a.dim), ‖w‖ = 1 → extensionBudget a w ≤ B

abbrev source5 : Prop := type_of% (@original_local_budget_iff.{v})

theorem source_bridge_5 : source5.{v} ↔ arena5.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_5 : arena5.{v}.Law actual.{v} :=
  source_bridge_5.mp (@original_local_budget_iff.{v})

end Reg.D5.S3.Quantum.Foundation.OriginalComparisonTopology
