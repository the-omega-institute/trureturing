import D5.S3.Quantum.Foundation.OriginalExclusionLimits
import Reg.D5.S3.Quantum.Foundation.ReciprocalPureCompactness

/-! Exact original source reconstruction with the original pure-comparison observation.
Variation, sensitivity and observational dependence are unfinished. No validated
four-slot registration or source-selection certificate is asserted. -/
noncomputable section
universe v
open Set Filter Topology TopologicalSpace

namespace Reg.D5.S3.Quantum.Foundation.OriginalExclusionLimits
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.ReciprocalExclusionLimits
open _root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
open Reg.D5.S3.Quantum.Foundation.ReciprocalPureCompactness

abbrev discontinuityArena : Arena where
  signature := pureCompactSignature.{v}
  Law O := ∀ P : Inputs.{v}, ∀ hc : IsClosed (P.cone : Set P.V),
    ∀ hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x,
    ∀ hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤,
    ∀ h3 : threeBallExclusions P.cone P.unit,
    (∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p)) →
    ∀ p : pure P.cone P.unit,
    ¬ ContinuousAt (wholeExclusion hc hs hg (ballHyp h3)) p →
    ∃ pn : ℕ → pure P.cone P.unit, Tendsto pn atTop (𝓝 p) ∧
      ∃ q : pure P.cone P.unit, (q : P.V) ∈ exclusion P.cone P.unit p ∧
        Tendsto (fun n => Metric.hausdorffDist (exclusion P.cone P.unit (pn n)) {(q : P.V)})
          atTop (𝓝 0)

abbrev discontinuitySource : Prop := type_of% (@original_discontinuity_collapse.{v})

theorem discontinuity_source_bridge : discontinuitySource.{v} ↔
    discontinuityArena.{v}.Law pureCompactActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem discontinuity_actual_positive : discontinuityArena.{v}.Law pureCompactActual.{v} :=
  discontinuity_source_bridge.mp (@original_discontinuity_collapse.{v})

abbrev diameterArena : Arena where
  signature := pureCompactSignature.{v}
  Law O := ∀ P : Inputs.{v}, IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → threeBallExclusions P.cone P.unit →
    (∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p)) →
    UpperSemicontinuous (fun p : pure P.cone P.unit => Metric.diam (exclusion P.cone P.unit p))

abbrev diameterSource : Prop := type_of% (@original_diameter_upperSemicontinuous.{v})

theorem diameter_source_bridge : diameterSource.{v} ↔ diameterArena.{v}.Law pureCompactActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem diameter_actual_positive : diameterArena.{v}.Law pureCompactActual.{v} :=
  diameter_source_bridge.mp (@original_diameter_upperSemicontinuous.{v})

abbrev baireArena : Arena where
  signature := pureCompactSignature.{v}
  Law O := ∀ P : Inputs.{v}, IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → threeBallExclusions P.cone P.unit →
    (∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p)) →
    IsOpen (regularRegion P.cone P.unit) ∧ Dense (regularRegion P.cone P.unit) ∧
      IsClosed (regularRegion P.cone P.unit)ᶜ ∧
        interior (closure (regularRegion P.cone P.unit)ᶜ) = ∅

abbrev baireSource : Prop := type_of% (@original_baire_regular_region.{v})

theorem baire_source_bridge : baireSource.{v} ↔ baireArena.{v}.Law pureCompactActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem baire_actual_positive : baireArena.{v}.Law pureCompactActual.{v} :=
  baire_source_bridge.mp (@original_baire_regular_region.{v})

abbrev regularArena : Arena where
  signature := pureCompactSignature.{v}
  Law O := ∀ P : Inputs.{v}, ∀ hc : IsClosed (P.cone : Set P.V),
    ∀ hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x,
    ∀ hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤,
    ∀ h3 : threeBallExclusions P.cone P.unit,
    (∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p)) →
    ∀ p : pure P.cone P.unit, p ∈ regularRegion P.cone P.unit ↔
      ContinuousAt (wholeExclusion hc hs hg (ballHyp h3)) p

abbrev regularSource : Prop := type_of% (@original_regular_iff_continuous.{v})

theorem regular_source_bridge : regularSource.{v} ↔ regularArena.{v}.Law pureCompactActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem regular_actual_positive : regularArena.{v}.Law pureCompactActual.{v} :=
  regular_source_bridge.mp (@original_regular_iff_continuous.{v})

end Reg.D5.S3.Quantum.Foundation.OriginalExclusionLimits
