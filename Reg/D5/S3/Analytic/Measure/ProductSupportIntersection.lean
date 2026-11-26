module

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Measure.ProductSupportIntersection
import Reg.Support.DependentFamily

@[expose] public section

open _root_.D5.S3.Analytic.Measure.ProductSupportIntersection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Filter
open scoped ENNReal

namespace Reg.D5.S3.Analytic.Measure.ProductSupportIntersection
noncomputable section
universe u v

abbrev signature : Signature where
  Params := Σ I : Type u, Σ X : I → Type v, Set I × Set I
  State p := (∀ i, p.2.1 i) → ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

open Classical in
def actual : Realization (signature.{u,v}) :=
  realize signature (fun _ p h => decide (DependsOn h (p.2.2.1 ∩ p.2.2.2)))
    (fun e => nomatch e)

private def rejected : Realization (signature.{u,v}) :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- The full original telescope, with only the supported-representative predicate observed. -/
def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {I : Type u} [Fintype I] {X : I → Type v} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {f g : (∀ i, X i) → ℝ≥0∞} (S T : Set I)
    (_hf : Measurable f) (_hg : Measurable g)
    (_hSf : DependsOn f S) (_hTg : DependsOn g T)
    (_he : f =ᵐ[MeasureTheory.Measure.pi μ] g),
    ∃ h : (∀ i, X i) → ℝ≥0∞, Measurable h ∧
      R.readout () ⟨I, X, S, T⟩ h = true ∧
      h =ᵐ[MeasureTheory.Measure.pi μ] f ∧ h =ᵐ[MeasureTheory.Measure.pi μ] g

private theorem source_bridge :
    (type_of% (@exists_measurable_intersection_representative.{u,v})) ↔ arena.Law actual := by
  simp only [arena, actual, realize, decide_eq_true_eq]

private theorem rejected_law : ¬ arena.Law (rejected.{u,v}) := by
  intro H
  let I := ULift.{u} Empty
  let X : I → Type v := fun _ => ULift.{v} Unit
  letI : Fintype I := inferInstance
  letI : ∀ i, MeasurableSpace (X i) := fun _ => ⊤
  let μ : ∀ i, MeasureTheory.Measure (X i) := fun i => nomatch i.down
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i => nomatch i.down
  obtain ⟨h, _, hh, _⟩ := H μ (f := fun _ => 0) (g := fun _ => 0) ∅ ∅
    measurable_const measurable_const (dependsOn_const 0) (dependsOn_const 0)
    Filter.EventuallyEq.rfl
  change false = true at hh
  cases hh

private theorem sensitivity : Sensitivity (arena.{u,v}) actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim
  · intro e
    exact nomatch e

private theorem dependence : ObservationalDependence (signature.{u,v}) actual := by
  intro i
  let I := ULift.{u} Unit
  let X : I → Type v := fun _ => ULift.{v} Bool
  let p : signature.Params := ⟨I, X, ∅, ∅⟩
  let f : (∀ i, X i) → ℝ≥0∞ := fun _ => 0
  let g : (∀ i, X i) → ℝ≥0∞ := fun x => if (x ⟨()⟩).down then 1 else 0
  have hf : DependsOn f (∅ : Set I) := dependsOn_const 0
  have hg : ¬ DependsOn g (∅ : Set I) := by
    intro hd
    have he := hd.empty (fun _ => ⟨false⟩) (fun _ => ⟨true⟩)
    norm_num [g] at he
  refine ⟨p, f, g, ?_⟩
  simp [actual, realize, p, hf, hg]

def family : Registration (arena.{u,v})
    (type_of% (@exists_measurable_intersection_representative.{u,v})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@exists_measurable_intersection_representative.{u,v}),
    rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_measurable_intersection_representative.{u,v})
    (Realization (signature.{u,v})) Unit Unit where
  unitName := `D5.S3.Analytic.Measure.ProductSupportIntersection.exists_measurable_intersection_representative.audit
  realizationName := `Reg.D5.S3.Analytic.Measure.ProductSupportIntersection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p h => decide (DependsOn h (p.2.2.1 ∩ p.2.2.2)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Measure.ProductSupportIntersection
    definition := none
    coordinates := #[0, 2, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Measure.ProductSupportIntersection
