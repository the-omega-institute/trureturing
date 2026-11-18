import D5.S3.Quantum.Foundation.ExclusionBallBundle
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Whole-family Hausdorff readouts with the complete original cone telescope. -/

noncomputable section
open Set Metric
universe v

namespace Reg.D5.S3.Quantum.Foundation.ExclusionBallBundle

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness
open _root_.D5.S3.Quantum.Foundation.ExclusionBallBundle
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  [nontrivial : Nontrivial V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite Inputs.nontrivial

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
  realize signature (fun _ P z => hausdorffDist
    (exclusion P.cone P.unit z.1) (exclusion P.cone P.unit z.2))
    (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
      (hg : Submodule.span ℝ (C : Set V) = ⊤)
      (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
      (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1),
      ∀ p : pure C u, ∀ ε > 0, ∃ δ > 0, ∀ q : pure C u,
        dist q p < δ → O.readout () P (q,p) < ε

abbrev sourceScope : Prop := type_of%
  (@_root_.D5.S3.Quantum.Foundation.ExclusionBallBundle.whole_exclusion_continuous.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    dsimp only
    intro hc hs hg hEB3 hW1
    exact Metric.continuous_iff.mp
      (@h P.V P.add P.space P.finite P.nontrivial P.cone P.unit hc hs hg hEB3 hW1)
  · intro h V add space finite nontrivial C u hc hs hg hEB3 hW1
    exact Metric.continuous_iff.mpr
      (h (@Inputs.mk V add space finite nontrivial C u) hc hs hg hEB3 hW1)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp
    (@_root_.D5.S3.Quantum.Foundation.ExclusionBallBundle.whole_exclusion_continuous.{v})

abbrev centerSignature : Signature where
  Params := Inputs.{v}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def centerActual : Realization centerSignature.{v} :=
  realize centerSignature (fun _ _ x => x) (fun a => nomatch a)

abbrev centerArena : Arena where
  signature := centerSignature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
      (hg : Submodule.span ℝ (C : Set V) = ⊤)
      (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
      (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1),
      Continuous (fun p => O.readout () P (chartCenter hEB3 p)) ∧
      ∀ p : pure C u, O.readout () P (chartCenter hEB3 p) ∈ base C u ∧
        ∀ a : ExclusionChart C u p, a.param 0 = O.readout () P (chartCenter hEB3 p)

abbrev centerSourceScope : Prop := type_of%
  (@_root_.D5.S3.Quantum.Foundation.ExclusionBallBundle.original_center_continuous.{v})

theorem center_source_bridge : centerSourceScope.{v} ↔
    centerArena.{v}.Law centerActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
  · intro h V add space finite nontrivial C u
    exact h (@Inputs.mk V add space finite nontrivial C u)

theorem center_actual_positive : centerArena.{v}.Law centerActual.{v} :=
  center_source_bridge.mp
    (@_root_.D5.S3.Quantum.Foundation.ExclusionBallBundle.original_center_continuous.{v})

end Reg.D5.S3.Quantum.Foundation.ExclusionBallBundle
