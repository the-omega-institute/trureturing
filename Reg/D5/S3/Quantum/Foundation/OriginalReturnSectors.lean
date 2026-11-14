import D5.S3.Quantum.Foundation.OriginalReturnSectors
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact original source telescopes and dependent readouts.
The source bridges do not supply whole-family variation, sensitivity,
observational dependence or occurrence-bound source selection. -/
noncomputable section
open Set Filter Topology
universe v
namespace Reg.D5.S3.Quantum.Foundation.OriginalReturnSectors
open _root_.D5.S3.Quantum.Foundation
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open SingleLabelNormalBody OriginalReturnSectors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
attribute [instance] Inputs.add Inputs.space Inputs.finite

structure EuclideanInputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [inner : InnerProductSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
attribute [instance] EuclideanInputs.add EuclideanInputs.inner EuclideanInputs.finite

structure ChartInputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  point : pure cone unit
  chart : ExclusionChart cone unit point
attribute [instance] ChartInputs.add ChartInputs.space ChartInputs.finite

namespace whole_return_leakage
abbrev signature : Signature where
  Params := Inputs.{v}
  State P := pure P.cone P.unit × pure P.cone P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P st => leakage P.cone P.unit st.1 st.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    {δ : ℝ} (hδ : 0 < δ),
    ∃ ε : ℝ, 0 < ε ∧ ∀ r t : pure C u,
      dist (r : V) y < ε → (t : V) ∈ exclusion C u r → O.readout () P (p,t) < δ

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalReturnSectors.whole_return_leakage.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalReturnSectors.whole_return_leakage.{v})

abbrev Pending := Registration arena.{v} sourceScope.{v}
end whole_return_leakage

namespace uniform_return_sectors
abbrev signature : Signature where
  Params := Inputs.{v}
  State P := pure P.cone P.unit × pure P.cone P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P st => leakage P.cone P.unit st.1 st.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (a : ExclusionChart C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (_hb : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ),
    ∃ ε θ H : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < H ∧
      ∀ r t : pure C u, dist (r:V) y < ε → (t:V) ∈ exclusion C u r →
        Module.finrank ℝ (affineSpan ℝ (exclusion C u t)).direction ≤ a.dim →
        ∃ i : Fin (a.dim+1), ∀ f : V →L[ℝ] ℝ,
          f ≠ 0 → (∀ x ∈ C, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
          ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
          ‖slope a f‖ ≤ H * baseMaximum C u f * O.readout () P (p,t)

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalReturnSectors.uniform_return_sectors.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalReturnSectors.uniform_return_sectors.{v})

abbrev Pending := Registration arena.{v} sourceScope.{v}
end uniform_return_sectors

namespace source_contact_simplex
abbrev signature : Signature where
  Params := ChartInputs.{v}
  State P := EuclideanSpace ℝ (Fin P.chart.dim)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P z => P.chart.param z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : ChartInputs.{v}, ∀ {y : P.V},
    y ∈ intrinsicInterior ℝ (exclusion P.cone P.unit P.point) →
    ∃ (ξ : EuclideanSpace ℝ (Fin P.chart.dim))
      (b : AffineBasis (Fin (P.chart.dim+1)) ℝ (EuclideanSpace ℝ (Fin P.chart.dim))),
      O.readout () P ξ = y ∧ ‖ξ‖ < 1 ∧ (∀ i, ‖b i‖ = 1) ∧
      (∀ i, 0 < b.coord i ξ) ∧ AffineIndependent ℝ (fun i => O.readout () P (b i)) ∧
      Module.finrank ℝ (affineSpan ℝ (exclusion P.cone P.unit P.point)).direction = P.chart.dim ∧
      LinearMap.range P.chart.param.linear ≤ LinearMap.ker P.unit
abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalReturnSectors.source_contact_simplex.{v})
theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.point P.chart
  · intro h V add space finite C u p a
    exact h (@ChartInputs.mk V add space finite C u p a)
theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalReturnSectors.source_contact_simplex.{v})
abbrev Pending := Registration arena.{v} sourceScope.{v}
end source_contact_simplex

namespace original_return_geometry
abbrev signature : Signature where
  Params := EuclideanInputs.{v}
  State P := pure P.cone P.unit × pure P.cone P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P st => leakage P.cone P.unit st.1 st.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : EuclideanInputs.{v},
    let E := P.V
    let C₁ := P.cone
    let u₁ := P.unit
    ∀ (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {y : E} (hy : y ∈ intrinsicInterior ℝ (exclusion C₁ u₁ p))
    (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (hb : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ),
    ∃ ε θ H β η : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < H ∧ 0 < β ∧ 0 < η ∧
      η = 1-(1-β/(Metric.diam (base C₁ u₁)/2))^2 ∧
      β < Metric.diam (base C₁ u₁)/2 ∧
      (∀ r t : pure C₁ u₁, dist (r:E) y < ε → (t:E) ∈ exclusion C₁ u₁ r →
        Module.finrank ℝ (affineSpan ℝ (exclusion C₁ u₁ t)).direction ≤ a.dim →
        ∃ i : Fin (a.dim+1), ∀ f : E →L[ℝ] ℝ,
          f ≠ 0 → (∀ x ∈ C₁, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
          ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
          ‖slope a f‖ ≤ H*baseMaximum C₁ u₁ f*O.readout () P (p,t)) ∧
      ∀ (r t : ℕ → pure C₁ u₁), Tendsto (fun n => (r n:E)) atTop (𝓝 y) →
        (∀ n, (t n:E) ∈ exclusion C₁ u₁ (r n)) →
        (∀ᶠ n in atTop, sectorViolation a b (t n) θ H) →
        ∀ (c : ∀ n, ExclusionChart C₁ u₁ (t n))
          (z : ∀ n, EuclideanSpace ℝ (Fin (c n).dim)),
          (∀ n, (c n).param (z n) = r n) →
          Tendsto (fun n => O.readout () P (p,t n)) atTop (𝓝 0) ∧
          (∀ n, ‖z n‖ = 1 ∧ 0 < (c n).dim ∧
            (c n).dim ≤ Module.finrank ℝ (LinearMap.ker u₁) ∧
            ‖(c n).param.linear.toContinuousLinearMap‖ ≤ Metric.diam (base C₁ u₁)/2) ∧
          (∀ᶠ n in atTop, a.dim+1 ≤ (c n).dim ∧
            Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
              sourceProjection p a '' exclusion C₁ u₁ (t n) ∧
            1-(1-(β-dist (r n:E) y)/(Metric.diam (base C₁ u₁)/2))^2 ≤
              ‖(projectedLinear p (c n)).ker.starProjection (z n)‖^2 ∧
            β ≤ (c n).param.linear.singularValues (a.dim-1) ∧
            (c n).param.linear.singularValues a.dim ≤ O.readout () P (p,t n)) ∧
          β ≤ liminf (fun n => (c n).param.linear.singularValues (a.dim-1)) atTop ∧
          η ≤ liminf (fun n => ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖^2) atTop

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalReturnSectors.original_return_geometry.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.inner P.finite P.cone P.unit
  · intro h E add inner finite C₁ u₁
    exact h (@EuclideanInputs.mk E add inner finite C₁ u₁)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalReturnSectors.original_return_geometry.{v})

abbrev Pending := Registration arena.{v} sourceScope.{v}
end original_return_geometry

end Reg.D5.S3.Quantum.Foundation.OriginalReturnSectors
