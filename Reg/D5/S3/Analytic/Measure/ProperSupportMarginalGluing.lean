import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Analytic.Measure.ProperSupportMarginalGluing
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-! The dependent state retains arbitrary coordinate types. The law retains the
complete product-measure telescope and all concrete marginal-factorization data. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Function Finset Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Measure.ProperSupportMarginalGluing
open scoped ENNReal BigOperators Classical

namespace Reg.D5.S3.Analytic.Measure.ProperSupportMarginalGluing
section Proper
universe u v w

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
    {J : Type w} (s : Finset I) (S : J → Finset I)
    (f : J → (∀ i, X i) → ℝ≥0∞),
    (∀ j, Measurable (f j)) → (∀ j, DependsOn (f j) (S j)) →
    (∀ j, 0 < ∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ) →
    (∀ j, (∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ) ≠ ∞) →
    (∀ j, S j ⊆ s) → (∀ j, S j ≠ s) →
    (∀ k ∈ s, ∃ h : ∀ i, X i → ℝ≥0∞,
      (∀ i, Measurable (h i)) ∧ (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j, lmarginal μ {k} (f j) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => (∫⁻ y, f j y ∂MeasureTheory.Measure.pi μ) *
          ∏ i ∈ (S j).erase k, h i (x i))) →
    ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
      (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j, R.readout () ⟨I, X⟩ (f j) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => (∫⁻ y, f j y ∂MeasureTheory.Measure.pi μ) *
          ∏ i ∈ S j, h i (x i))

theorem source_bridge :
    (type_of% @exists_common_profiles_of_deleted_marginal_factorizations.{u,v,w}) ↔
      arena.{u,v,w}.Law actual := Iff.rfl

theorem actual_law : arena.{u,v,w}.Law actual :=
  @exists_common_profiles_of_deleted_marginal_factorizations.{u,v,w}

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  classical
  intro law
  let I := ULift.{u} (Fin 2)
  let J := ULift.{w} Unit
  let X (_ : I) := ULift.{v} Unit
  let μ : ∀ i : I, MeasureTheory.Measure (X i) := fun _ => MeasureTheory.Measure.dirac ⟨()⟩
  haveI (i : I) : IsProbabilityMeasure (μ i) := inferInstance
  have hl : ∀ k ∈ (univ : Finset I), ∃ h : ∀ i, X i → ℝ≥0∞,
      (∀ i, Measurable (h i)) ∧ (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j : J, lmarginal μ {k} (fun _ => (1 : ℝ≥0∞)) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => (∫⁻ y : ∀ i, X i, (1 : ℝ≥0∞) ∂MeasureTheory.Measure.pi μ) *
          ∏ i ∈ (∅ : Finset I).erase k, (1 : ℝ≥0∞)) := by
    intro k hk
    refine ⟨fun _ _ => 1, fun _ => measurable_const, ?_, ?_⟩
    · intro i; simp
    · intro j
      filter_upwards [] with x
      change (∫⁻ _y : (∀ i : ({k} : Finset I), X i), (1 : ℝ≥0∞)
        ∂MeasureTheory.Measure.pi (fun i : ({k} : Finset I) => μ i)) = _
      simp
  obtain ⟨h, hm, hu, he⟩ := law μ (univ : Finset I) (fun _ : J => ∅)
    (fun _ _ => (1 : ℝ≥0∞)) (fun _ => measurable_const)
    (by intro j x y hxy; rfl) (by intro j; simp) (by intro j; simp)
    (by intro j; exact empty_subset _) (by intro j; exact Finset.univ_nonempty.ne_empty.symm) hl
  have H := he (⟨()⟩ : J)
  have hn : ¬ ((0 : ℝ≥0∞) = 1) := by norm_num
  simpa [rejected, realize] using H

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  let I := ULift.{u} Unit
  let X (_ : I) := ULift.{v} Unit
  refine ⟨⟨I, X⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have H := congrFun he (fun _ => ⟨()⟩)
  norm_num [actual, realize] at H

def family : Registration arena.{u,v,w}
    (type_of% @exists_common_profiles_of_deleted_marginal_factorizations.{u,v,w}) where
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
    (@exists_common_profiles_of_deleted_marginal_factorizations.{u,v,w})
    (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Analytic.Measure.ProperSupportMarginalGluing.exists_common_profiles_of_deleted_marginal_factorizations.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Measure.ProperSupportMarginalGluing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨family.{u,v,w}⟩
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

end Proper

abbrev equalityArena.{w,u,v} : Arena where
  signature := signature.{u,v}
  Law R := ∀ {I : Type u} [Fintype I] {X : I → Type v} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {J : Type w} [Fintype J] (S : J → Finset I)
    (f : J → (∀ i, X i) → ℝ≥0∞) (wgt : J → ℝ),
    (∀ j, Measurable (f j)) → (∀ j, DependsOn (f j) (S j)) →
    (∀ j, 0 < ∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ) →
    (∀ j, (∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ) ≠ ∞) →
    (∀ j, 0 < wgt j) →
    (∀ i, ∑ j ∈ univ.filter (fun j => i ∈ S j), wgt j = 1) →
    (∀ a b, (∀ j, a ∈ S j ↔ b ∈ S j) → a = b) →
    ((∫⁻ x, ∏ j, f j x ^ wgt j ∂MeasureTheory.Measure.pi μ) =
      ∏ j, (∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ) ^ wgt j ↔
    ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
      (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j, R.readout () ⟨I, X⟩ (f j) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => (∫⁻ y, f j y ∂MeasureTheory.Measure.pi μ) *
          ∏ i ∈ S j, h i (x i)))

theorem equality_source_bridge.{w,u,v} :
    (type_of% @finner_equality_iff_common_profiles.{w,u,v}) ↔
      equalityArena.{w,u,v}.Law actual := Iff.rfl

private theorem equalityRejectedLaw.{w,u,v} : ¬ equalityArena.{w,u,v}.Law rejected := by
  classical
  intro law
  let I := ULift.{u} Empty
  let J := ULift.{w} Unit
  let X (_ : I) := ULift.{v} Unit
  let μ : ∀ i : I, MeasureTheory.Measure (X i) := fun _ => MeasureTheory.Measure.dirac ⟨()⟩
  haveI (i : I) : IsProbabilityMeasure (μ i) := inferInstance
  have H := law μ (fun _ : J => ∅) (fun _ _ => (1 : ℝ≥0∞)) (fun _ => (2 : ℝ))
    (fun _ => measurable_const) (by intro j x y hxy; rfl)
    (by intro j; simp) (by intro j; simp) (by intro j; norm_num)
    (by intro i; exact nomatch i.down) (by intro a; exact nomatch a.down)
  obtain ⟨h, hm, hu, he⟩ := H.mp (by simp)
  have hr := he (⟨()⟩ : J)
  simpa [rejected, realize] using hr

def equalityFamily.{w,u,v} : Registration equalityArena.{w,u,v}
    (type_of% @finner_equality_iff_common_profiles.{w,u,v}) where
  actual := actual
  bridge := equality_source_bridge.{w,u,v}
  variation := ⟨@finner_equality_iff_common_profiles.{w,u,v}, rejected, equalityRejectedLaw.{w,u,v}⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, equalityRejectedLaw.{w,u,v}⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def equalityRegistration.{w,u,v} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finner_equality_iff_common_profiles.{w,u,v})
    (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Analytic.Measure.ProperSupportMarginalGluing.finner_equality_iff_common_profiles.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Measure.ProperSupportMarginalGluing.equalityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨equalityArena.{w,u,v}⟩
  objectArena := .source ⟨equalityArena.{w,u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equalityArena.{w,u,v} ⟨equalityFamily.{w,u,v}⟩
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

end Reg.D5.S3.Analytic.Measure.ProperSupportMarginalGluing
