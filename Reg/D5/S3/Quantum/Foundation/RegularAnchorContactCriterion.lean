import D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
import Reg.D5.S3.Quantum.Foundation.RegularAnchorNormalChart

/-! Exact original-family reconstruction from the original gap readout. Whole-family
variation, sensitivity and observational dependence require additional evidence. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.Quantum.Foundation.RegularAnchorNormalChart
open _root_.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev Inputs := RegularAnchorNormalChart.Inputs.{v}
abbrev signature := RegularAnchorNormalChart.signature.{v}
abbrev actual := RegularAnchorNormalChart.actual.{v}

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → EB3 P.cone P.unit →
    Function.Injective (fun p : pure P.cone P.unit => exclusion P.cone P.unit p) →
    common P.cone P.unit P.p P.effect → Regular P.cone P.unit P.p →
    ∃ k : P.V →ₗ[ℝ] ℝ,
      (∀ x, k x = P.unit x - O.readout () P x) ∧
      ∃ n : NativeChart P.cone P.unit P.p k P.chart, ContactCriterion n

abbrev sourceScope : Prop := type_of% (@regular_anchor_contact_criterion.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hs hg h3 hinj he hreg
    refine ⟨P.effect,?_,?_⟩
    · intro x
      change P.effect x = P.unit x - (P.unit x - P.effect x)
      ring
    · exact @h P.V P.add P.space P.finite P.cone P.unit hc hs hg h3 hinj
        P.p P.effect he hreg P.chart
  · intro h V add space finite C u hc hs hg h3 hinj p e he hreg a
    obtain ⟨k,hk,hn⟩ := h (@RegularAnchorNormalChart.Inputs.mk V add space finite C u p e a)
      hc hs hg h3 hinj he hreg
    have hke : k = e := by
      ext x
      have hx := hk x
      change k x = u x - (u x - e x) at hx
      linarith
    simpa only [hke] using hn

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@regular_anchor_contact_criterion.{v})

end Reg.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
