import D5.S3.Quantum.Foundation.OriginalRowSaturation
import Reg.D5.S3.Quantum.Foundation.OriginalBallScale

/-! Exact original telescopes and actual-positive source reconstruction.
The scoped observation is original pure reciprocity. Whole-family variation,
sensitivity and observational dependence are unfinished; these arenas are not
validated four-slot registrations. -/
noncomputable section
universe v
open Set Filter Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace Reg.D5.S3.Quantum.Foundation.OriginalRowSaturation
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OriginalFacePolarity
open _root_.D5.S3.Quantum.Foundation.OriginalBallScale
open _root_.D5.S3.Quantum.Foundation.OriginalNormalFamily
open _root_.D5.S3.Quantum.Foundation.OriginalRowSaturation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight
open Reg.D5.S3.Quantum.Foundation.OriginalBallScale

abbrev arena0 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hc : IsClosed (P.cone : Set P.V)) (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (h3 : _root_.D5.S3.Quantum.Foundation.ReciprocalExclusionLimits.threeBallExclusions P.cone P.unit)
    (hPR : ∀ s t : pure P.cone P.unit, O.readout () P (s,t) = O.readout () P (t,s))
    (p q : pure P.cone P.unit) (pn : ℕ → pure P.cone P.unit) (hp : Tendsto pn atTop (𝓝 p))
    (hcollapse : Tendsto (fun n => Metric.hausdorffDist
      (exclusion P.cone P.unit (pn n)) {(q : P.V)}) atTop (𝓝 0)) , PureEdgeRow p q

abbrev source0 : Prop := type_of% (@actual_collapse_pure_edge_row.{v})

theorem source_bridge_0 : source0.{v} ↔ arena0.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_0 : arena0.{v}.Law actual.{v} :=
  source_bridge_0.mp (@actual_collapse_pure_edge_row.{v})

abbrev arena1 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hc : IsClosed (P.cone : Set P.V)) (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hEB3 : ∀ s : pure P.cone P.unit, ∃ b : ExclusionChart P.cone P.unit s, b.dim = 3)
    (hPR : ∀ s t : pure P.cone P.unit, O.readout () P (s,t) = O.readout () P (t,s))
    (hInj : Function.Injective (fun s : pure P.cone P.unit => exclusion P.cone P.unit s))
    (p : pure P.cone P.unit) (a : ExclusionChart P.cone P.unit p) (ha : a.dim = 3)
    (ep : P.V →ₗ[ℝ] ℝ) (hp : ∀ e, e ∈ fullZeroConfirmers P.cone P.unit p ↔ e = ep)
    (q : pure P.cone P.unit) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q)
    (pn : ℕ → pure P.cone P.unit) (hpn : Tendsto pn atTop (𝓝 p))
    (hcollapse : Tendsto (fun n => Metric.hausdorffDist
      (exclusion P.cone P.unit (pn n)) {(q : P.V)}) atTop (𝓝 0)) ,
    (∀ w : chartSpace a, ‖w‖ = 1 → extensionBudget a w = 1) ∧
    (∀ b : ExclusionChart P.cone P.unit q, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) ∧
    (∀ x ∈ base P.cone P.unit, comparison P.cone P.unit p x = ep x) ∧
    (∀ f : P.V →ₗ[ℝ] ℝ, confirms P.cone P.unit p f → ∀ x ∈ P.cone, ep x ≤ f x) ∧
    (∀ w : chartSpace a, ‖w‖ = 1 → ∀ s : pure P.cone P.unit, a.param w = s →
      ∀ z : chartSpace a, ‖z‖ ≤ 1 → comparison P.cone P.unit s (a.param z) = (1 + ⟪w,z⟫) / 2) ∧
    (∀ b : ExclusionChart P.cone P.unit q, ∀ w : chartSpace b, ‖w‖ = 1 →
      ∀ s : pure P.cone P.unit, b.param w = s → ∀ z : chartSpace b, ‖z‖ ≤ 1 →
        comparison P.cone P.unit s (b.param z) = (1 + ⟪w,z⟫) / 2)

abbrev source1 : Prop := type_of% (@original_row_saturation.{v})

theorem source_bridge_1 : source1.{v} ↔ arena1.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_1 : arena1.{v}.Law actual.{v} :=
  source_bridge_1.mp (@original_row_saturation.{v})

abbrev arena2 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hc : IsClosed (P.cone : Set P.V)) (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hEB3 : ∀ s : pure P.cone P.unit, ∃ b : ExclusionChart P.cone P.unit s, b.dim = 3)
    (hPR : ∀ s t : pure P.cone P.unit, O.readout () P (s,t) = O.readout () P (t,s))
    (hInj : Function.Injective (fun s : pure P.cone P.unit => exclusion P.cone P.unit s))
    (p : pure P.cone P.unit) (a : ExclusionChart P.cone P.unit p) (ha : a.dim = 3)
    (ep : P.V →ₗ[ℝ] ℝ) (hp : ∀ e, e ∈ fullZeroConfirmers P.cone P.unit p ↔ e = ep)
    (v : chartSpace a) (hv : ‖v‖ = 1) (hbudget : 1 < extensionBudget a v) ,
    ContinuousAt (_root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.wholeExclusion hc hs hg
      (fun s => ⟨(hEB3 s).choose⟩)) p

abbrev source2 : Prop := type_of% (@original_nonunit_continuity.{v})

theorem source_bridge_2 : source2.{v} ↔ arena2.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_2 : arena2.{v}.Law actual.{v} :=
  source_bridge_2.mp (@original_nonunit_continuity.{v})

abbrev arena3 : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀
    (hc : IsClosed (P.cone : Set P.V)) (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hEB3 : ∀ s : pure P.cone P.unit, ∃ b : ExclusionChart P.cone P.unit s, b.dim = 3)
    (hPR : ∀ s t : pure P.cone P.unit, O.readout () P (s,t) = O.readout () P (t,s))
    (hInj : Function.Injective (fun s : pure P.cone P.unit => exclusion P.cone P.unit s))
    (p : pure P.cone P.unit) (hSigma : p ∉ _root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.regularRegion P.cone P.unit) ,
    p ∉ uniqueFullZero P.cone P.unit ∨
      ∃ ep : P.V →ₗ[ℝ] ℝ, (∀ e, e ∈ fullZeroConfirmers P.cone P.unit p ↔ e = ep) ∧
        (∀ b : ExclusionChart P.cone P.unit p, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) ∧
        (∀ x ∈ base P.cone P.unit, comparison P.cone P.unit p x = ep x) ∧
        (∀ f : P.V →ₗ[ℝ] ℝ, confirms P.cone P.unit p f → ∀ x ∈ P.cone, ep x ≤ f x) ∧
        (∀ (q : pure P.cone P.unit) (pn : ℕ → pure P.cone P.unit), Tendsto pn atTop (𝓝 p) →
          Tendsto (fun n => Metric.hausdorffDist (exclusion P.cone P.unit (pn n)) {(q : P.V)}) atTop (𝓝 0) →
          ∀ b : ExclusionChart P.cone P.unit q, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1)

abbrev source3 : Prop := type_of% (@original_discontinuity_branches.{v})

theorem source_bridge_3 : source3.{v} ↔ arena3.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_3 : arena3.{v}.Law actual.{v} :=
  source_bridge_3.mp (@original_discontinuity_branches.{v})

end Reg.D5.S3.Quantum.Foundation.OriginalRowSaturation
