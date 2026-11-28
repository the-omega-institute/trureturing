import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Analytic.Measure.ProductSupportIntersection
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-! The law retains the exact finite-product marginal congruence telescope,
including the original measurable functions and their almost-everywhere equality. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Function Finset Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Measure.ProductSupportIntersection
open scoped ENNReal BigOperators Classical

namespace Reg.D5.S3.Analytic.Measure.ProductSupportIntersection
universe u v

abbrev signature : Signature where
  Params := Σ I : Type u, I → Type v
  State p := (∀ i, p.2 i) → ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (∀ i, p.2 i) → ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {I : Type u} [Fintype I] {X : I → Type v} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    [DecidableEq I] (s : Finset I) {f g : (∀ i, X i) → ℝ≥0∞},
    Measurable f → Measurable g → (f =ᵐ[MeasureTheory.Measure.pi μ] g) →
    lmarginal μ s (R.readout () ⟨I, X⟩ f) =ᵐ[MeasureTheory.Measure.pi μ]
      lmarginal μ s g

theorem source_bridge :
    (type_of% @marginal_congr_ae.{u,v}) ↔ arena.{u,v}.Law actual := Iff.rfl

theorem actual_law : arena.{u,v}.Law actual := @marginal_congr_ae.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro law
  let I := ULift.{u} Unit
  let X (_ : I) := ULift.{v} Unit
  let μ : ∀ i : I, MeasureTheory.Measure (X i) := fun _ => MeasureTheory.Measure.dirac ⟨()⟩
  haveI (i : I) : IsProbabilityMeasure (μ i) := inferInstance
  have H := law μ ∅ (f := fun _ => 1) (g := fun _ => 1)
    measurable_const measurable_const Filter.EventuallyEq.rfl
  simpa [rejected, realize] using H

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  let I := ULift.{u} Unit
  let X (_ : I) := ULift.{v} Unit
  refine ⟨⟨I, X⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have H := congrFun he (fun _ => ⟨()⟩)
  norm_num [actual, realize] at H

def family : Registration arena.{u,v}
    (type_of% @marginal_congr_ae.{u,v}) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@marginal_congr_ae.{u,v})
    (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Analytic.Measure.ProductSupportIntersection.marginal_congr_ae.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Measure.ProductSupportIntersection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Measure.ProductSupportIntersection
