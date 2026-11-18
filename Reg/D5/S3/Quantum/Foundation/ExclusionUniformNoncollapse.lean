import D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The exact original telescope as a dependent family of norm readouts.
Whole-family intervention, sensitivity and source selection remain separate obligations. -/

noncomputable section
open Set
universe v

namespace Reg.D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness
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
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)

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
      ∃ η > 0, ∀ (p : pure C u) (a : ExclusionChart C u p), a.dim = 3 →
        ∀ v, η * ‖v‖ ≤ O.readout () P (a.param.linear v)

abbrev sourceScope : Prop := type_of%
  (@_root_.D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse.all_label_uniform_noncollapse.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
  · intro h V add space finite nontrivial C u
    exact h (@Inputs.mk V add space finite nontrivial C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp
    (@_root_.D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse.all_label_uniform_noncollapse.{v})

end Reg.D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse
