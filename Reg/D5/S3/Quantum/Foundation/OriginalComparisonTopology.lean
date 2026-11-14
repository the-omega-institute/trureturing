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

abbrev scalarArena0 : Arena where
  signature := scalarSignature.{v}
  Law O := ∀ P : ScalarInputs.{v}, ∀ (pn : ℕ → pure P.cone P.unit) (p : pure P.cone P.unit)
    (ht : Tendsto (fun n => (fun s => (O.readout () P s).1) (pn n)) atTop (𝓝 ((fun s => (O.readout () P s).1) p))),
    Tendsto (fun n => (fun s => (O.readout () P s).2.1) (pn n)) atTop (𝓝 ((fun s => (O.readout () P s).2.1) p))

abbrev scalarSource0 : Prop := type_of% (@original_whole_limit_calibration.{v})

theorem scalar_source_bridge_0 : scalarSource0.{v} ↔ scalarArena0.{v}.Law scalarActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict
      P.generating P.balls P.reciprocal
  · intro h V add space finite C u hc hs hg h3 hPR
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, h3, hPR⟩

theorem scalar_actual_positive_0 : scalarArena0.{v}.Law scalarActual.{v} :=
  scalar_source_bridge_0.mp (@original_whole_limit_calibration.{v})

abbrev scalarArena1 : Arena where
  signature := scalarSignature.{v}
  Law O := ∀ P : ScalarInputs.{v}, ∀ (pn : ℕ → pure P.cone P.unit) (q : P.V)
    (ht : Tendsto (fun n => (fun s => (O.readout () P s).1) (pn n)) atTop (𝓝 ({q} : NonemptyCompacts P.V))),
    Tendsto (fun n => (fun s => (O.readout () P s).2.1) (pn n)) atTop (𝓝 0) ∧
      Tendsto (fun n => (fun s => (O.readout () P s).2.2) (pn n)) atTop atTop

abbrev scalarSource1 : Prop := type_of% (@original_singleton_limit_scalars.{v})

theorem scalar_source_bridge_1 : scalarSource1.{v} ↔ scalarArena1.{v}.Law scalarActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict
      P.generating P.balls P.reciprocal
  · intro h V add space finite C u hc hs hg h3 hPR
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, h3, hPR⟩

theorem scalar_actual_positive_1 : scalarArena1.{v}.Law scalarActual.{v} :=
  scalar_source_bridge_1.mp (@original_singleton_limit_scalars.{v})

abbrev scalarArena2 : Arena where
  signature := scalarSignature.{v}
  Law O := ∀ P : ScalarInputs.{v}, ∀ (pn : ℕ → pure P.cone P.unit) (p : pure P.cone P.unit)
    (hp : Tendsto pn atTop (𝓝 p)),
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((Tendsto (fun n => (fun s => (O.readout () P s).1) (pn (φ n))) atTop (𝓝 ((fun s => (O.readout () P s).1) p)) ∧
        Tendsto (fun n => (fun s => (O.readout () P s).2.1) (pn (φ n))) atTop (𝓝 ((fun s => (O.readout () P s).2.1) p)) ∧
        Tendsto (fun n => (fun s => (O.readout () P s).2.2) (pn (φ n))) atTop (𝓝 ((fun s => (O.readout () P s).2.2) p))) ∨
      ∃ q : pure P.cone P.unit, (q:P.V) ∈ exclusion P.cone P.unit p ∧
        Tendsto (fun n => (fun s => (O.readout () P s).1) (pn (φ n))) atTop (𝓝 ({(q:P.V)} : NonemptyCompacts P.V)) ∧
        Tendsto (fun n => (fun s => (O.readout () P s).2.1) (pn (φ n))) atTop (𝓝 0) ∧
        Tendsto (fun n => (fun s => (O.readout () P s).2.2) (pn (φ n))) atTop atTop)

abbrev scalarSource2 : Prop := type_of% (@original_scalar_subsequence.{v})

theorem scalar_source_bridge_2 : scalarSource2.{v} ↔ scalarArena2.{v}.Law scalarActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict
      P.generating P.balls P.reciprocal
  · intro h V add space finite C u hc hs hg h3 hPR
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, h3, hPR⟩

theorem scalar_actual_positive_2 : scalarArena2.{v}.Law scalarActual.{v} :=
  scalar_source_bridge_2.mp (@original_scalar_subsequence.{v})

abbrev scalarArena3 : Arena where
  signature := scalarSignature.{v}
  Law O := ∀ P : ScalarInputs.{v}, UpperSemicontinuous (fun s => (O.readout () P s).2.1)

abbrev scalarSource3 : Prop := type_of% (@original_calibration_upperSemicontinuous.{v})

theorem scalar_source_bridge_3 : scalarSource3.{v} ↔ scalarArena3.{v}.Law scalarActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict
      P.generating P.balls P.reciprocal
  · intro h V add space finite C u hc hs hg h3 hPR
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, h3, hPR⟩

theorem scalar_actual_positive_3 : scalarArena3.{v}.Law scalarActual.{v} :=
  scalar_source_bridge_3.mp (@original_calibration_upperSemicontinuous.{v})

abbrev scalarArena4 : Arena where
  signature := scalarSignature.{v}
  Law O := ∀ P : ScalarInputs.{v}, LowerSemicontinuous (fun s => (O.readout () P s).2.2)

abbrev scalarSource4 : Prop := type_of% (@original_optimalBudget_lowerSemicontinuous.{v})

theorem scalar_source_bridge_4 : scalarSource4.{v} ↔ scalarArena4.{v}.Law scalarActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict
      P.generating P.balls P.reciprocal
  · intro h V add space finite C u hc hs hg h3 hPR
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, h3, hPR⟩

theorem scalar_actual_positive_4 : scalarArena4.{v}.Law scalarActual.{v} :=
  scalar_source_bridge_4.mp (@original_optimalBudget_lowerSemicontinuous.{v})

abbrev scalarArena5 : Arena where
  signature := scalarSignature.{v}
  Law O := ∀ P : ScalarInputs.{v}, ∀ (p : pure P.cone P.unit)
    (hp : ¬ ContinuousAt (fun s => (O.readout () P s).1) p),
    ∃ pn : ℕ → pure P.cone P.unit, Tendsto pn atTop (𝓝 p) ∧
      ∃ q : pure P.cone P.unit, (q:P.V) ∈ exclusion P.cone P.unit p ∧
        Tendsto (fun n => (fun s => (O.readout () P s).1) (pn n)) atTop (𝓝 ({(q:P.V)} : NonemptyCompacts P.V)) ∧
        Tendsto (fun n => (fun s => (O.readout () P s).2.1) (pn n)) atTop (𝓝 0) ∧
        Tendsto (fun n => (fun s => (O.readout () P s).2.2) (pn n)) atTop atTop

abbrev scalarSource5 : Prop := type_of% (@original_discontinuity_scalar_witness.{v})

theorem scalar_source_bridge_5 : scalarSource5.{v} ↔ scalarArena5.{v}.Law scalarActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict
      P.generating P.balls P.reciprocal
  · intro h V add space finite C u hc hs hg h3 hPR
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, h3, hPR⟩

theorem scalar_actual_positive_5 : scalarArena5.{v}.Law scalarActual.{v} :=
  scalar_source_bridge_5.mp (@original_discontinuity_scalar_witness.{v})

/- The full dependent family above reconstructs the source and reads its actual
scalar outputs. A lawful enrolled readout, sourceSelection, Variation, Sensitivity
and ObservationalDependence are still required for Contract.Registration.
No four-slot registration or validated status is asserted. -/

end Reg.D5.S3.Quantum.Foundation.OriginalComparisonTopology
