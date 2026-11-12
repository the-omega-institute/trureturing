import D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Registration for the proved whole-base branch of VII98.7.

The remaining segment-face and positive-dimensional-facet classification
branches are intentionally absent from this arena; this registration records
the exact branch proved by the Lean source.  It is not a declaration_validated
claim for the complete VII98.7 atom.
-/

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.WholePairBallConfirmation
open _root_.D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type u
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ →
    ∀ {p q : P.V} (b : BallChart C u p q), pairBase C u p q = base C u →
      ∀ n, ‖n‖ = 1 →
        ∃ f, confirms C u (b.param n) f ∧ f (b.param (-n)) = 0

abbrev sourceScope : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ),
    IsClosed (C : Set V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set V) = ⊤ →
    ∀ {p q : V} (b : BallChart C u p q), pairBase C u p q = base C u →
    ∀ {n : EuclideanSpace ℝ (Fin b.dim)}, ‖n‖ = 1 →
      ∃ f : V →ₗ[ℝ] ℝ,
        confirms C u (b.param n) f ∧ f (b.param (-n)) = 0

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    dsimp only
    intro hc hu hs p q b hb n hn
    exact @h P.V P.add P.space P.finite P.cone P.unit hc hu hs p q b hb n hn
  · intro h V add space finite C u hc hu hs p q b hb n hn
    exact @h (@Inputs.mk V add space finite C u) hc hu hs p q b hb n hn

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (by
    intro V add space finite C u hc hu hs p q b hb n hn
    exact ball_chart_antipodal_effect C u hc hu b hb hn)

end Reg.D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly
