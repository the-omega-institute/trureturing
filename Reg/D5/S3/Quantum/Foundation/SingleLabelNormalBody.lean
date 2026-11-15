import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full original source telescopes reconstructed from whole-body and native-dimension
readouts. Four-slot registrations additionally require lawful enrolled templates,
whole-family interventions, sensitivity, observational dependence and source selection. -/

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Foundation.SingleLabelNormalBody
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.SingleLabelNormalBody
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type u
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  p : pure cone unit
  chart : ExclusionChart cone unit p
attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set (EuclideanSpace ℝ (Fin P.chart.dim)) ×
    (EuclideanSpace ℝ (Fin P.chart.dim) → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P _ => (slopeBody P.chart, gap P.chart)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → exclusionBalls P.cone P.unit →
    SingleLabel P.cone P.unit P.p →
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧
      Metric.closedBall 0 rho ⊆ (O.readout () P ()).1 ∧
      ∀ n : EuclideanSpace ℝ (Fin P.chart.dim), ‖n‖ = 1 →
        (O.readout () P ()).2 n ≤ (1-rho)/(1+rho) ∧ (1-rho)/(1+rho) < 1 ∧
        ((O.readout () P ()).2 n = 0 ↔ n ∈ (O.readout () P ()).1)

abbrev sourceScope : Prop := type_of% (@uniform_original_gap.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P hc hs hg hB hp
    exact @h P.V P.add P.space P.finite P.cone P.unit hc hs hg hB P.p hp P.chart
  · intro h V add space finite C unit hc hs hg hB p hp a
    exact h (@Inputs.mk V add space finite C unit p a) hc hs hg hB hp

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@uniform_original_gap.{u})

structure DimensionInputs extends Inputs.{u} where
  q : pure cone unit
  neighbor : ExclusionChart cone unit q

abbrev dimensionSignature : Signature where
  Params := DimensionInputs.{u}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def dimensionActual : Realization dimensionSignature.{u} :=
  realize dimensionSignature (fun _ P _ => Module.finrank ℝ P.V) (fun e => nomatch e)

abbrev dimensionArena : Arena where
  signature := dimensionSignature.{u}
  Law O := ∀ P : DimensionInputs.{u},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → exclusionBalls P.cone P.unit →
    SingleLabel P.cone P.unit P.p → (P.q : P.V) ∈ exclusion P.cone P.unit P.p →
    P.chart.dim + P.neighbor.dim + 1 ≤ O.readout () P ()

abbrev dimensionSourceScope : Prop := type_of% (@native_dimension.{u})

theorem dimension_source_bridge :
    dimensionSourceScope.{u} ↔ dimensionArena.{u}.Law dimensionActual.{u} := by
  constructor
  · intro h P hc hs hg hB hp hq
    exact @h P.V P.add P.space P.finite P.cone P.unit hc hs hg hB P.p hp
      P.chart P.q hq P.neighbor
  · intro h V add space finite C unit hc hs hg hB p hp a q hq bq
    exact h ⟨@Inputs.mk V add space finite C unit p a, q, bq⟩ hc hs hg hB hp hq

theorem dimension_actual_positive : dimensionArena.{u}.Law dimensionActual.{u} :=
  dimension_source_bridge.mp (@native_dimension.{u})

end Reg.D5.S3.Quantum.Foundation.SingleLabelNormalBody
