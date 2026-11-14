import D5.S3.Quantum.Foundation.CommonSourceLiftObstruction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact reconstruction of all original source telescopes. Whole-family
variation, sensitivity, observational dependence and source selection are separate obligations. -/

noncomputable section
universe v
namespace Reg.D5.S3.Quantum.Foundation.CommonSourceLiftObstruction

open Set Filter Topology
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.SingleLabelNormalBody
open _root_.D5.S3.Quantum.Foundation.CommonSourceLiftObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
attribute [instance] Inputs.add Inputs.space Inputs.finite

structure Geometry extends Inputs.{v} where
  closed : IsClosed (cone : Set V)
  strict : ∀ z ∈ cone, z ≠ 0 → 0 < unit z
  generating : Submodule.span ℝ (cone : Set V) = ⊤
  balls : exclusionBalls cone unit

namespace Control
abbrev signature : Signature where
  Params := Geometry.{v}
  State P := P.V →ₗ[ℝ] ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P b => baseMaximum (C := P.cone) (u := P.unit) b)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Geometry.{v}, ∀ p : pure P.cone P.unit,
    ∃ A : ℝ, 0 < A ∧
      (∀ b : P.V →ₗ[ℝ] ℝ, ‖b.toContinuousLinearMap‖ ≤ A *
        _root_.D5.S3.Quantum.Foundation.FixedZeroObstruction.stateNorm P.closed P.strict b) ∧
      Tendsto (upperDisplacement p) (𝓝 p) (𝓝 0) ∧
      ∀ t : pure P.cone P.unit, A * upperDisplacement p t < 1 →
        ∀ b : P.V →ₗ[ℝ] ℝ, (∀ z ∈ P.cone, 0 ≤ b z) → b t = 0 →
          O.readout () P b ≤
            _root_.D5.S3.Quantum.Foundation.FixedZeroObstruction.faceMaximum p b /
              (1 - A * upperDisplacement p t)

abbrev sourceScope : Prop := type_of% (@moving_positive_control.{v})
theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict P.generating P.balls
  · intro h V add space finite C u hc hs hg hB
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, hB⟩

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@moving_positive_control.{v})
end Control

namespace Normalization
abbrev signature : Signature where
  Params := Geometry.{v}
  State P := P.V →ₗ[ℝ] ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.V →ₗ[ℝ] ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P b => normalizePositive (C := P.cone) (u := P.unit) b)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Geometry.{v},
    ∀ (p : pure P.cone P.unit) (t : ℕ → pure P.cone P.unit), Tendsto t atTop (𝓝 p) →
    ∀ b : ℕ → P.V →ₗ[ℝ] ℝ, (∀ n z, z ∈ P.cone → 0 ≤ b n z) →
    (∀ n, b n (t n) = 0) → ∀ ell : exclusion P.cone P.unit p → ℝ,
    (∀ x, 0 ≤ ell x ∧ ell x ≤ 1) →
    TendstoUniformly (fun n (x : exclusion P.cone P.unit p) => b n x) ell atTop →
    (∀ n, proper P.cone P.unit (O.readout () P (b n)) ∧ O.readout () P (b n) (t n) = 0) ∧
    Tendsto (fun n => _root_.D5.S3.Quantum.Foundation.FixedZeroObstruction.stateNorm
      P.closed P.strict (O.readout () P (b n) - b n)) atTop (𝓝 0) ∧
    TendstoUniformly (fun n (x : exclusion P.cone P.unit p) =>
      O.readout () P (b n) x) ell atTop ∧
    (sSup (Set.range ell) = 1 →
      Tendsto (fun n => baseMaximum (C := P.cone) (u := P.unit) (b n)) atTop (𝓝 1))

abbrev sourceScope : Prop := type_of% (@moving_positive_normalization.{v})
theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict P.generating P.balls
  · intro h V add space finite C u hc hs hg hB
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, hB⟩

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@moving_positive_normalization.{v})
end Normalization

namespace Shrinking
abbrev signature : Signature where
  Params := Geometry.{v}
  State P := pure P.cone P.unit × P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ z => ‖z.2 - z.1.val‖) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Geometry.{v}, ∀ p : pure P.cone P.unit, SingleLabel P.cone P.unit p →
    ∀ y : P.V, y ∈ intrinsicInterior ℝ (exclusion P.cone P.unit p) →
    ∀ r : ℕ → pure P.cone P.unit, Tendsto (fun n => (r n : P.V)) atTop (𝓝 y) →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ exclusion P.cone P.unit (r n), O.readout () P (p, x) < ε

abbrev sourceScope : Prop := type_of% (@single_label_mixed_shrinking.{v})
theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict P.generating P.balls
  · intro h V add space finite C u hc hs hg hB
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, hB⟩

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@single_label_mixed_shrinking.{v})
end Shrinking

namespace Obstruction
abbrev signature : Signature where
  Params := Geometry.{v}
  State P := pure P.cone P.unit × pure P.cone P.unit × (P.V →ₗ[ℝ] ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P z => sourceDistance P.closed P.strict P.generating P.balls
    z.1 z.2.1 z.2.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Geometry.{v}, ∀ p : pure P.cone P.unit, SingleLabel P.cone P.unit p →
    ∀ y : P.V, y ∈ intrinsicInterior ℝ (exclusion P.cone P.unit p) →
    ∃ m : ℕ, 0 < m ∧ ∃ a : Fin m → pure P.cone P.unit,
    ∃ h : Fin m → P.V →ₗ[ℝ] ℝ,
      (∀ i, (a i : P.V) ∈ exclusion P.cone P.unit p ∧
        h i ∈ _root_.D5.S3.Quantum.Foundation.FixedZeroObstruction.fullZeroConfirmers
          P.cone P.unit (a i)) ∧
      (∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
        ∀ r : pure P.cone P.unit, ‖(r : P.V) - y‖ < ε →
          ∀ t : pure P.cone P.unit, (t : P.V) ∈ exclusion P.cone P.unit r →
            Module.finrank ℝ (affineSpan ℝ (exclusion P.cone P.unit p)).direction + 1 ≤
                Module.finrank ℝ (affineSpan ℝ (exclusion P.cone P.unit t)).direction ∨
              ∃ i, δ ≤ O.readout () P (p, t, h i)) ∧
      (∀ τ : ℝ, 0 < τ → ∃ ε : ℝ, 0 < ε ∧
        ∀ r : pure P.cone P.unit, ‖(r : P.V) - y‖ < ε →
          ∀ t : pure P.cone P.unit, (t : P.V) ∈ exclusion P.cone P.unit r → ∀ i, h i t ≤ τ)

abbrev sourceScope : Prop := type_of% (@finite_common_source_obstruction.{v})
theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.closed P.strict P.generating P.balls
  · intro h V add space finite C u hc hs hg hB
    exact h ⟨@Inputs.mk V add space finite C u, hc, hs, hg, hB⟩

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@finite_common_source_obstruction.{v})
end Obstruction

end Reg.D5.S3.Quantum.Foundation.CommonSourceLiftObstruction
