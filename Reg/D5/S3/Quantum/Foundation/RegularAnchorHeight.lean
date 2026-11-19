import D5.S3.Quantum.Foundation.RegularAnchorHeight
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source reconstruction for original regular-anchor conclusions.
Whole-family interventions and observational sensitivity remain separate. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.FixedZeroObstruction
open _root_.D5.S3.Quantum.Foundation.RegularAnchorHeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev confirmationSignature : Signature where
  Params := Inputs.{v}
  State P := P.V →L[ℝ] ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.V →L[ℝ] ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def confirmationActual : Realization confirmationSignature.{v} :=
  realize confirmationSignature (fun _ _ f => f) (fun e => nomatch e)

abbrev confirmationArena : Arena where
  signature := confirmationSignature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set P.V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x),
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    Function.Injective (fun p : pure C u => exclusion C u p) →
    ∀ (p : pure C u) (ep : P.V →ₗ[ℝ] ℝ),
    (∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep) → ZeroContinuousAt hc hs p →
    ∀ (pn : ℕ → pure C u), Tendsto (fun n => (pn n : P.V)) atTop (𝓝 (p : P.V)) →
    ∀ en : ℕ → (P.V →ₗ[ℝ] ℝ), (∀ n, en n ∈ fullZeroConfirmers C u (pn n)) →
    Tendsto (fun n => O.readout () P (en n).toContinuousLinearMap)
      atTop (𝓝 (O.readout () P ep.toContinuousLinearMap))

abbrev confirmationScope : Prop := type_of% (@regular_confirmation_tendsto.{v})

theorem confirmation_source_bridge :
    confirmationScope.{v} ↔ confirmationArena.{v}.Law confirmationActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem confirmation_actual_positive : confirmationArena.{v}.Law confirmationActual.{v} :=
  confirmation_source_bridge.mp (@regular_confirmation_tendsto.{v})

abbrev heightSignature : Signature where
  Params := Inputs.{v}
  State P := (P.V →ₗ[ℝ] ℝ) × P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def heightActual : Realization heightSignature.{v} :=
  realize heightSignature (fun _ _ z => z.1 z.2) (fun e => nomatch e)

abbrev heightArena : Arena where
  signature := heightSignature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set P.V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x),
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    Function.Injective (fun p : pure C u => exclusion C u p) →
    ∀ (p : pure C u) (ep : P.V →ₗ[ℝ] ℝ),
    RegularAnchor hc hs p → ep ∈ fullZeroConfirmers C u p →
    ∀ ε : ℝ, 0 < ε → ∃ σ : ℝ, 0 < σ ∧
    ∀ (a : pure C u) (ea : P.V →ₗ[ℝ] ℝ), ea ∈ fullZeroConfirmers C u a →
      (∃ z ∈ exclusion C u p, ε ≤ O.readout () P (ea, z)) →
        σ ≤ O.readout () P (u - ep, (a : P.V))

abbrev heightScope : Prop := type_of% (@regular_anchor_uniform_height.{v})

theorem height_source_bridge : heightScope.{v} ↔ heightArena.{v}.Law heightActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem height_actual_positive : heightArena.{v}.Law heightActual.{v} :=
  height_source_bridge.mp (@regular_anchor_uniform_height.{v})

end Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight
