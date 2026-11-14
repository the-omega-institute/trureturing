import D5.S3.Quantum.Foundation.OriginalNormalFamily
import Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight
import Reg.D5.S3.Quantum.Foundation.ReciprocalPureCompactness

/-! Complete original telescope with its actual scalar comparison readout.
Whole-family intervention, sensitivity and observational dependence are separate obligations. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.OriginalBallScale

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OriginalBallScale
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight
open scoped RealInnerProductSpace

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := P.V × P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P z => comparison P.cone P.unit z.1 z.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    (∀ s t : pure C u, comparison C u s t = comparison C u t s) →
    ∀ (p : pure C u) (a : ExclusionChart C u p),
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
      ∀ b : ExclusionChart C u p, ∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 →
      (BudgetFeasible b v (1 / (2*t)) ∧
        (∀ M, BudgetFeasible b v M → 1 / (2*t) ≤ M) ∧ extensionBudget b v = 1 / (2*t)) ∧
      ∀ q : pure C u, b.param v = q → ∃ e : P.V →ₗ[ℝ] ℝ,
        confirms C u q e ∧ (∀ z, e (b.param z) = 1-t+t*⟪v,z⟫) ∧
        ∀ z, ‖z‖ ≤ 1 → O.readout () P (q, b.param z) = 1-t+t*⟪v,z⟫

abbrev sourceScope : Prop := type_of% (@original_common_chart_scale.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@original_common_chart_scale.{v})

end Reg.D5.S3.Quantum.Foundation.OriginalBallScale

open Set Filter Topology TopologicalSpace

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

abbrev continuityArena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    (∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p)) →
    Continuous (fun z : pure P.cone P.unit × pure P.cone P.unit =>
      O.readout () P (z.1, z.2))

abbrev continuitySource : Prop := type_of% (@pure_comparison_continuous.{v})

theorem source_bridge_continuity : continuitySource.{v} ↔ continuityArena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive_continuity : continuityArena.{v}.Law actual.{v} :=
  source_bridge_continuity.mp (@pure_comparison_continuous.{v})

/- These exact source bridges do not supply a lawful enrolled readout,
sourceSelection, Variation, Sensitivity or ObservationalDependence. -/

end Reg.D5.S3.Quantum.Foundation.OriginalComparisonTopology

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

/-- The whole original EB3 family, including its actual hypotheses. -/
structure ScalarInputs extends Inputs.{v} where
  closed : IsClosed (cone : Set V)
  strict : ∀ x ∈ cone, x ≠ 0 → 0 < unit x
  generating : Submodule.span ℝ (cone : Set V) = ⊤
  balls : _root_.D5.S3.Quantum.Foundation.ReciprocalExclusionLimits.threeBallExclusions cone unit
  reciprocal : ∀ p q : pure cone unit, comparison cone unit p q = comparison cone unit q p

abbrev scalarSignature : Signature where
  Params := ScalarInputs.{v}
  State P := pure P.cone P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := NonemptyCompacts P.V × ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def scalarActual : Realization scalarSignature.{v} :=
  realize scalarSignature (fun _ P p =>
    (_root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.wholeExclusion
      P.closed P.strict P.generating
      (_root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.ballHyp P.balls) p,
    calibration P.closed P.strict P.generating
      (_root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.ballHyp P.balls) P.reciprocal p,
    optimalBudget P.closed P.strict P.generating
      (_root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.ballHyp P.balls) P.reciprocal p))
    (fun e => nomatch e)

abbrev scalarArena : Arena where
  signature := scalarSignature.{v}
  Law O := ∀ P : ScalarInputs.{v}, ∀ p : pure P.cone P.unit,
    let A := fun s => (O.readout () P s).2.1
    let B := fun s => (O.readout () P s).2.2
    (p ∈ _root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.regularRegion P.cone P.unit ↔
      ContinuousAt A p) ∧
    (p ∈ _root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.regularRegion P.cone P.unit ↔
      ContinuousAt B p) ∧
    UpperSemicontinuous A ∧ LowerSemicontinuous B ∧
    (p ∈ _root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.regularRegion P.cone P.unit ↔
      ∃ U : Set (pure P.cone P.unit), IsOpen U ∧ p ∈ U ∧ ∃ t : ℝ, 0 < t ∧
        ∀ s ∈ U, B s ≤ t) ∧
    (∀ S : Set (pure P.cone P.unit), IsCompact S →
      S ⊆ _root_.D5.S3.Quantum.Foundation.OriginalExclusionLimits.regularRegion P.cone P.unit →
      ∃ t : ℝ, ∀ s ∈ S, B s ≤ t) ∧
    (0 < A p ∧ A p ≤ 1/2 ∧
      ∀ b : ExclusionChart P.cone P.unit p,
      ∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 →
        BudgetFeasible b v (B p) ∧
          (∀ M, BudgetFeasible b v M → B p ≤ M) ∧ extensionBudget b v = B p)

abbrev scalarSource : Prop := type_of% (@original_common_continuity_sets.{v})

theorem scalar_source_bridge : scalarSource.{v} ↔ scalarArena.{v}.Law scalarActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict
      P.generating P.balls P.reciprocal
  · intro h V add space finite C u hc hs hg h3 hPR
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, h3, hPR⟩

theorem scalar_actual_positive : scalarArena.{v}.Law scalarActual.{v} :=
  scalar_source_bridge.mp (@original_common_continuity_sets.{v})

/- The full dependent family above reconstructs the source and reads its actual
scalar outputs. A lawful enrolled readout, sourceSelection, Variation, Sensitivity
and ObservationalDependence are still required for Contract.Registration.
No four-slot registration or validated status is asserted. -/

end Reg.D5.S3.Quantum.Foundation.OriginalComparisonTopology
