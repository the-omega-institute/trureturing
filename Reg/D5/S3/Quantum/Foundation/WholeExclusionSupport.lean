import D5.S3.Quantum.Foundation.WholeExclusionSupport
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact original support telescope and its enrolled dependent realization.
Intervention, sensitivity and source-selection evidence remain unsupplied. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.WholeExclusionSupport

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.WholeExclusionSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  point : pure cone unit
  candidate : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{v}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.V →ₗ[ℝ] ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P _ => P.candidate) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let h := O.readout () P ()
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    h P.point = 1 →
    (∀ x ∈ P.cone, h x ≤ P.unit x) →
    (∀ x ∈ exclusion P.cone P.unit P.point, h x = 0) →
    confirms P.cone P.unit P.point h

abbrev sourceScope : Prop := type_of% (@whole_exclusion_support.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    dsimp only
    intro hc hs hr hu hz
    exact @h P.V P.add P.space P.finite P.cone P.unit hc hs P.point P.candidate hr hu hz
  · intro h V add space finite C u hc hs r f hr hu hz
    exact h (@Inputs.mk V add space finite C u r f) hc hs hr hu hz

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@whole_exclusion_support.{v})

/-- This observation family cannot supply a failing intervention: every
linear-map readout satisfies its conditional support law. -/
theorem every_realization_positive (O : Realization signature.{v}) : arena.{v}.Law O := by
  intro P
  dsimp only
  exact whole_exclusion_support (r := P.point) (h := O.readout () P ())



namespace Facet

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  [nontrivial : Nontrivial V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  [pureFinite : Finite (pure cone unit)]

attribute [instance] Inputs.add Inputs.space Inputs.finite Inputs.nontrivial Inputs.pureFinite

abbrev signature : Signature where
  Params := Inputs.{v}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set (PointedCone.Face P.cone)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

def erased : Realization signature.{v} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    ∃ F : facets P.cone, F.1 ∈ O.readout () P ()

abbrev sourceScope : Prop := type_of% (@finite_pure_facet.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hs hg
    obtain ⟨F⟩ := @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
      P.pureFinite hc hs hg
    exact ⟨F, Set.mem_univ _⟩
  · intro h V add space finite nontrivial C u pureFinite hc hs hg
    obtain ⟨F, _⟩ := h (@Inputs.mk V add space finite nontrivial C u pureFinite) hc hs hg
    exact ⟨F⟩

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@finite_pure_facet.{v})

/-- Removing every native face makes the law fail at each original admissible
input; this is a genuine variation of the observation, not a proof of enrollment. -/
theorem erased_negative (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) : ¬ arena.{v}.Law erased.{v} := by
  intro h
  obtain ⟨F, hF⟩ := h P hc hs hg
  exact hF

end Facet

end Reg.D5.S3.Quantum.Foundation.WholeExclusionSupport
