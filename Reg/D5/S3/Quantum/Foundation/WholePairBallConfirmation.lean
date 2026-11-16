import D5.S3.Quantum.Foundation.WholePairBallConfirmation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact reconstruction of the original whole-ball theorem telescope. The
whole-family intervention, sensitivity, observational dependence and raw source
selector required for a complete four-slot registration are not supplied. -/

noncomputable section
universe u
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Foundation.WholePairBallConfirmation

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.WholePairBallConfirmation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type u
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  support : commonSupport cone unit

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := pure P.cone P.unit × P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x => supportEffect P.support x.1 x.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ →
    wholePairBalls C u →
    reciprocalLeast C u ∧ fullMixture C u ∧
    (∀ (p : pure C u) x, x ∈ base C u →
      (excludes C u p x ↔ O.readout () P (p, x) = 0)) ∧
    zeroMidpoint C u ∧ allAntipodes C u ∧
    (∀ (p : pure C u) (n : ℕ) (x : Fin n → P.V) (w : Fin n → ℝ),
      (∀ i, x i ∈ base C u) → (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
      (excludes C u p (∑ i, w i • x i) ↔
        ∀ i, 0 < w i → excludes C u p (x i)))

abbrev sourceScope : Prop := type_of% (@whole_pair_ball_confirmation.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    dsimp only
    intro hc hu hs hB
    exact @h P.V P.add P.space P.finite P.cone P.unit hc hu hs hB P.support
  · intro h V add space finite C u hc hu hs hB hH
    exact h (@Inputs.mk V add space finite C u hH) hc hu hs hB

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@whole_pair_ball_confirmation.{u})

end Reg.D5.S3.Quantum.Foundation.WholePairBallConfirmation
