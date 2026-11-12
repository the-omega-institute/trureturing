import D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Registration for the proved whole-base branch of VII98.7.

These source bridges record the proved branches. A lawful observation-dependent
four-slot registration is absent; no declared_validated claim is made for these
branches or the complete VII98.7 atom. The unfinished audit is tracked in issue
https://github.com/the-omega-institute/trureturing/issues/29630.
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
    ∀ {p q : P.V} (b : BallChart C u p q), pairBase C u p q = base C u →
      ∀ n, ‖n‖ = 1 →
        ∃ f, confirms C u (b.param n) f ∧ f (b.param (-n)) = 0

abbrev sourceScope : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ),
    IsClosed (C : Set V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    ∀ {p q : V} (b : BallChart C u p q), pairBase C u p q = base C u →
    ∀ {n : EuclideanSpace ℝ (Fin b.dim)}, ‖n‖ = 1 →
      ∃ f : V →ₗ[ℝ] ℝ,
        confirms C u (b.param n) f ∧ f (b.param (-n)) = 0

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    dsimp only
    intro hc hu p q b hb n hn
    exact @h P.V P.add P.space P.finite P.cone P.unit hc hu p q b hb n hn
  · intro h V add space finite C u hc hu p q b hb n hn
    exact @h (@Inputs.mk V add space finite C u) hc hu p q b hb n hn

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (by
    intro V add space finite C u hc hu p q b hb n hn
    exact ball_chart_antipodal_effect C u hc hu b hb hn)

abbrev segmentScope : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ),
    IsClosed (C : Set V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set V) = ⊤ →
    Module.finrank ℝ (vectorSpan ℝ (base C u)) ≤ 3 →
    (∀ p q : pure C u, p ≠ q → pairBase C u p q = segment ℝ (p : V) (q : V)) →
    Finite (pure C u) ∧
      _root_.D5.S3.Quantum.Foundation.FinitePureSimplex.simplex C u ∧
      Nat.card (pure C u) ≤ Module.finrank ℝ (vectorSpan ℝ (base C u)) + 1 ∧
      allAntipodes C u

abbrev segmentArena : Arena where
  signature := signature.{u}
  Law _ := ∀ P : Inputs.{u},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    Module.finrank ℝ (vectorSpan ℝ (base P.cone P.unit)) ≤ 3 →
    (∀ p q : pure P.cone P.unit, p ≠ q →
      pairBase P.cone P.unit p q = segment ℝ (p : P.V) (q : P.V)) →
    Finite (pure P.cone P.unit) ∧
      _root_.D5.S3.Quantum.Foundation.FinitePureSimplex.simplex P.cone P.unit ∧
      Nat.card (pure P.cone P.unit) ≤
        Module.finrank ℝ (vectorSpan ℝ (base P.cone P.unit)) + 1 ∧
      allAntipodes P.cone P.unit

theorem segment_source_bridge : segmentScope.{u} ↔ segmentArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact @h (@Inputs.mk V add space finite C u)

theorem segment_actual_positive : segmentArena.{u}.Law actual.{u} :=
  segment_source_bridge.mp (by
    intro V add space finite C u hc hu hs hd hseg
    exact segment_faces_lowdim_antipodes C u hc hu hs hd hseg)

end Reg.D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly
