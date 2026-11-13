import D5.S3.Quantum.Foundation.FixedZeroObstruction.MovingPositiveControl
import Reg.D5.S3.Quantum.Foundation.FixedZeroObstruction

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.FixedZeroObstruction.MovingPositiveControl

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.FixedZeroObstruction
open _root_.D5.S3.Quantum.Foundation.SingleLabelNormalBody
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev controlArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set P.V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x),
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    ∃ A : ℝ, 0 < A ∧
      (∀ b : P.V →ₗ[ℝ] ℝ, ‖b.toContinuousLinearMap‖ ≤ A * stateNorm hc hs b) ∧
      (∀ (p : pure C u) (tn : ℕ → pure C u), Filter.Tendsto tn Filter.atTop (nhds p) →
        Filter.Tendsto (fun n => sSup ((fun x => Metric.infDist x (O.readout () P p)) ''
          O.readout () P (tn n))) Filter.atTop (nhds 0)) ∧
      ∀ (p t : pure C u) (b : P.V →ₗ[ℝ] ℝ), b ∈ positiveZeros t →
        A * sSup ((fun x => Metric.infDist x (O.readout () P p)) '' O.readout () P t) < 1 →
        baseMaximum (C := C) (u := u) b ≤ sSup (b '' O.readout () P p) /
          (1 - A * sSup ((fun x => Metric.infDist x (O.readout () P p)) '' O.readout () P t))

abbrev controlScope : Prop := type_of% (@moving_positive_control.{u})

theorem control_source_bridge : controlScope.{u} ↔ controlArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem control_actual_positive : controlArena.{u}.Law actual.{u} :=
  control_source_bridge.mp (@moving_positive_control.{u})

abbrev normalizationArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set P.V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x),
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    ∀ (p : pure C u) (tn : ℕ → pure C u), Filter.Tendsto tn Filter.atTop (nhds p) →
    ∀ (bn : ℕ → (P.V →ₗ[ℝ] ℝ)), (∀ n, bn n ∈ positiveZeros (tn n)) →
    ∀ ell : O.readout () P p → ℝ, (∀ x, 0 ≤ ell x ∧ ell x ≤ 1) →
    TendstoUniformly (fun n (x : O.readout () P p) => bn n x) ell Filter.atTop →
    (∀ n, proper C u (unitTruncation (C := C) (u := u) (bn n)) ∧
      unitTruncation (C := C) (u := u) (bn n) (tn n) = 0) ∧
    TendstoUniformly (fun n (x : O.readout () P p) =>
      unitTruncation (C := C) (u := u) (bn n) x) ell Filter.atTop ∧
    Filter.Tendsto (fun n => stateNorm hc hs (unitTruncation (C := C) (u := u) (bn n) - bn n))
      Filter.atTop (nhds 0) ∧
    (sSup (Set.range ell) = 1 →
      Filter.Tendsto (fun n => baseMaximum (C := C) (u := u) (bn n)) Filter.atTop (nhds 1))

abbrev normalizationScope : Prop := type_of% (@moving_positive_normalization.{u})

theorem normalization_source_bridge : normalizationScope.{u} ↔ normalizationArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem normalization_actual_positive : normalizationArena.{u}.Law actual.{u} :=
  normalization_source_bridge.mp (@moving_positive_normalization.{u})

abbrev commonArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) → (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    ∀ p : pure C u, SingleLabel C u p →
    ∀ y : P.V, y ∈ intrinsicInterior ℝ (exclusion C u p) →
    ∃ (S : Finset P.V) (a : S → pure C u) (h : S → (P.V →ₗ[ℝ] ℝ)),
      S.Nonempty ∧
      (∀ i, (a i : P.V) = (i : P.V) ∧ (a i : P.V) ∈ O.readout () P p ∧
        h i ∈ fullZeroConfirmers C u (a i)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
        (∀ r : pure C u, ‖(r : P.V) - y‖ < ε →
          ∀ t : pure C u, (t : P.V) ∈ exclusion C u r →
          Module.finrank ℝ (affineSpan ℝ (O.readout () P p)).direction + 1 ≤
            Module.finrank ℝ (affineSpan ℝ (O.readout () P t)).direction ∨
          δ ≤ sSup (Set.range fun i => positiveSourceDistance p t (h i))) ∧
        ∀ τ : ℝ, 0 < τ → ∃ ετ : ℝ, 0 < ετ ∧
          ∀ r : pure C u, ‖(r : P.V) - y‖ < ετ →
            ∀ t : pure C u, (t : P.V) ∈ exclusion C u r → ∀ i, h i t ≤ τ

abbrev commonScope : Prop := type_of% (@common_positive_source_obstruction.{u})

theorem common_source_bridge : commonScope.{u} ↔ commonArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem common_actual_positive : commonArena.{u}.Law actual.{u} :=
  common_source_bridge.mp (@common_positive_source_obstruction.{u})

end Reg.D5.S3.Quantum.Foundation.FixedZeroObstruction.MovingPositiveControl
