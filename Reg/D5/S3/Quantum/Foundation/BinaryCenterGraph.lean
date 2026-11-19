import Reg.Support.DependentFamily
import D5.S3.Quantum.Foundation.BinaryCenterGraph

/-! Typed source and actual-law bridges for the affine center graph. -/

noncomputable section
universe v

open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation
open CircuitBalancedConfirmation FacetZeroGluing SingleLabelNormalBody ContinuousFrameSum
open ExclusionBallFaces OriginalFacePolarity BinaryCenterGeometry

namespace Reg.D5.S3.Quantum.Foundation.BinaryCenterGraph

abbrev CenterComparison : Signature where
  Params := Type v
  State V := V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := V → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization CenterComparison.{v} :=
  realize CenterComparison (fun _ _ x y => x = y) (fun e => nomatch e)

namespace whole_ball_center_affine

abbrev arena : Arena where
  signature := CenterComparison.{v}
  Law r :=
    ∀ {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
      (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
      (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
      (_hBC : binaryCompatible hB) (p : pure C u) (b : ExclusionChart C u p),
    ∃! g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
      (∀ x (hx : ‖x‖ = 1), r.readout () V (g x) (center hB (chartPure hc hs hg hB p b x hx))) ∧
      g '' Metric.closedBall 0 1 ⊆ base C u

theorem source_bridge : (type_of% @D5.S3.Quantum.Foundation.BinaryCenterGeometry.whole_ball_center_affine.{v}) ↔
    arena.{v}.Law actual.{v} := Iff.rfl

theorem actual_law : arena.{v}.Law actual.{v} :=
  source_bridge.mp @D5.S3.Quantum.Foundation.BinaryCenterGeometry.whole_ball_center_affine.{v}

end whole_ball_center_affine

namespace whole_ball_center_graph

abbrev arena : Arena where
  signature := CenterComparison.{v}
  Law r :=
    ∀ {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
      (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
      (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
      (_hBC : binaryCompatible hB) (p : pure C u) (b : ExclusionChart C u p),
    ∃ g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
      (∀ x (hx : ‖x‖ = 1), r.readout () V (g x) (center hB (chartPure hc hs hg hB p b x hx))) ∧
      g '' Metric.closedBall 0 1 ⊆ base C u ∧
      (∀ k : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
        (∀ x (hx : ‖x‖ = 1), r.readout () V (k x) (center hB (chartPure hc hs hg hB p b x hx))) → k = g) ∧
      (SingleLabel C u p → Function.Injective g ∧ Module.finrank ℝ g.linear.range = b.dim) ∧
      (¬ SingleLabel C u p → ∃ c : V, ∀ x, g x = c)

theorem source_bridge : (type_of% @D5.S3.Quantum.Foundation.BinaryCenterGeometry.whole_ball_center_graph.{v}) ↔
    arena.{v}.Law actual.{v} := Iff.rfl

theorem actual_law : arena.{v}.Law actual.{v} :=
  source_bridge.mp @D5.S3.Quantum.Foundation.BinaryCenterGeometry.whole_ball_center_graph.{v}

end whole_ball_center_graph

end Reg.D5.S3.Quantum.Foundation.BinaryCenterGraph
end
