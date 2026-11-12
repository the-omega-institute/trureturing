import D5.S3.Quantum.Foundation.MixedExclusionGeometry
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Original mixed-boundary label observations and their complete source telescope. -/

noncomputable section
universe v
namespace Reg.D5.S3.Quantum.Foundation.MixedExclusionGeometry

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.WholePairBallConfirmation
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.Quantum.Foundation.ContinuousFrameSum
open _root_.D5.S3.Quantum.Foundation.MixedExclusionGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  [nontrivial : Nontrivial V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  balls : exclusionBalls cone unit

attribute [instance] Inputs.add Inputs.space Inputs.finite Inputs.nontrivial

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := mixedExcluded P.cone P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := pure P.cone P.unit
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ x => label x) (fun e => nomatch e)

def outcome (P : Inputs.{v}) (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) (hW : weakPair P.cone P.unit)
    (σ : mixedExcluded P.cone P.unit → pure P.cone P.unit) : Prop :=
    (pure P.cone P.unit ⊆ intrinsicFrontier ℝ (base P.cone P.unit)) ∧
    mixedExcluded P.cone P.unit = intrinsicFrontier ℝ (base P.cone P.unit) \ pure P.cone P.unit ∧
    (∀ (x : mixedExcluded P.cone P.unit) (p : pure P.cone P.unit), σ x = p ↔
      (x : P.V) ∈ intrinsicInterior ℝ (exclusion P.cone P.unit p)) ∧
    Continuous (reflection hc hs hg P.balls hW) ∧
    Function.Involutive (reflection hc hs hg P.balls hW) ∧
    (∀ x : mixedExcluded P.cone P.unit, reflection hc hs hg P.balls hW x = x ↔
      x ∈ Set.range (centerSection hc hs hg P.balls)) ∧
    Continuous (σ) ∧
    Continuous (centerSection hc hs hg P.balls) ∧
    (∀ p : pure P.cone P.unit, σ (centerSection hc hs hg P.balls p) = p) ∧
    Continuous (contraction hc hs hg P.balls hW) ∧
    (∀ x : mixedExcluded P.cone P.unit,
      contraction hc hs hg P.balls hW (⟨0,by norm_num⟩,x) = x ∧
      contraction hc hs hg P.balls hW (⟨1,by norm_num⟩,x) = centerSection hc hs hg P.balls (σ x)) ∧
    (∀ (p : pure P.cone P.unit) (t : Set.Icc (0 : ℝ) 1),
      contraction hc hs hg P.balls hW (t,centerSection hc hs hg P.balls p) = centerSection hc hs hg P.balls p) ∧
    (∀ (p : pure P.cone P.unit) (t : Set.Icc (0 : ℝ) 1) (x : mixedExcluded P.cone P.unit),
      ((contraction hc hs hg P.balls hW (t,x) : mixedExcluded P.cone P.unit) : P.V) ∈ exclusion P.cone P.unit p ↔
        (x : P.V) ∈ exclusion P.cone P.unit p)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, ∀ (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) (hW : weakPair P.cone P.unit),
    outcome P hc hs hg hW (O.readout () P)

abbrev sourceScope : Prop := type_of% (@original_mixed_exclusion_contraction.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hs hg hW
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit hc hs hg P.balls hW
  · intro h V add space finite nontrivial C u hc hs hg hB hW
    exact h (@Inputs.mk V add space finite nontrivial C u hB) hc hs hg hW

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@original_mixed_exclusion_contraction.{v})

end Reg.D5.S3.Quantum.Foundation.MixedExclusionGeometry
