import D5.S3.Quantum.Foundation.FixedZeroObstruction.LocalPureLimit
import Reg.D5.S3.Quantum.Foundation.FixedZeroObstruction

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.FixedZeroObstruction.LocalPureLimit

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.SingleLabelNormalBody
open _root_.D5.S3.Quantum.Foundation.FixedZeroObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev collapseArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    ∀ p : pure C u, SingleLabel C u p →
    ∀ y : P.V, y ∈ intrinsicInterior ℝ (exclusion C u p) →
    ∀ rn : ℕ → pure C u,
      Filter.Tendsto (fun n => (rn n : P.V)) Filter.atTop (nhds y) →
      Filter.Tendsto (fun n => sSup ((fun x : P.V => ‖x - (p : P.V)‖) ''
        O.readout () P (rn n))) Filter.atTop (nhds 0)

abbrev collapseScope : Prop := type_of% (@local_single_label_collapse.{u})

theorem collapse_source_bridge : collapseScope.{u} ↔ collapseArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem collapse_actual_positive : collapseArena.{u}.Law actual.{u} :=
  collapse_source_bridge.mp (@local_single_label_collapse.{u})

end Reg.D5.S3.Quantum.Foundation.FixedZeroObstruction.LocalPureLimit
