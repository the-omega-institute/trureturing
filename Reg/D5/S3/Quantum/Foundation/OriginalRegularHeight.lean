import D5.S3.Quantum.Foundation.OriginalRegularHeight
import Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight

/-! The entire original theorem telescope is reconstructed by its actual
height and maximum readouts. Lawful family variation is a separate obligation. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.OriginalRegularHeight

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.FixedZeroObstruction
open _root_.D5.S3.Quantum.Foundation.RegularAnchorHeight
open _root_.D5.S3.Quantum.Foundation.OriginalRegularHeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight

abbrev endpointArena : Arena where
  signature := heightSignature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set P.V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x),
    Submodule.span ℝ (C : Set P.V) = ⊤ →
    (∀ q : pure C u, ∃ b : ExclusionChart C u q, b.dim = 3) →
    Function.Injective (fun q : pure C u => exclusion C u q) →
    ∀ (p : pure C u) (a : ExclusionChart C u p), a.dim = 3 →
    ∀ ep : P.V →ₗ[ℝ] ℝ, ep ∈ fullZeroConfirmers C u p → RegularAnchor hc hs p →
    ∃ σ : ℝ, 0 < σ ∧
      ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 →
      ∀ q : pure C u, a.param v = q →
      ∀ b : ExclusionChart C u q, b.dim = 3 →
      ∀ s : EuclideanSpace ℝ (Fin b.dim), ‖s‖ = 1 → b.param s = p →
      ∀ aa : pure C u, b.param (-s) = aa →
      ∀ ea : P.V →ₗ[ℝ] ℝ, ea ∈ fullZeroConfirmers C u aa →
        σ ≤ O.readout () P (u - ep, (aa : P.V)) ∧
        (aa : P.V) ∈ exclusion C u q ∧
        ∀ x ∈ exclusion C u q,
          O.readout () P (u - ep, x) ≤ O.readout () P (u - ep, (aa : P.V))

abbrev endpointScope : Prop := type_of% (@original_regular_height.{v})

theorem endpoint_source_bridge : endpointScope.{v} ↔ endpointArena.{v}.Law heightActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem endpoint_actual_positive : endpointArena.{v}.Law heightActual.{v} :=
  endpoint_source_bridge.mp (@original_regular_height.{v})

end Reg.D5.S3.Quantum.Foundation.OriginalRegularHeight
