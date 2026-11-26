import D5.S3.Analytic.Measure.ProperSupportMarginalGluing

open MeasureTheory Function Finset Filter
open scoped ENNReal BigOperators Classical
open D5.S3.Analytic.Measure.ProperSupportMarginalGluing

noncomputable section

-- An infinite row type: constant unit rows with empty supports in one active coordinate.
example {J : Type*} {X : Fin 1 → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
      (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j : J, (fun _ : ∀ i, X i => (1 : ℝ≥0∞)) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => ∏ i ∈ (∅ : Finset (Fin 1)), h i (x i)) := by
  have H := exists_common_profiles_of_deleted_marginal_factorizations μ
    (univ : Finset (Fin 1)) (fun _ : J => ∅) (fun _ _ => (1 : ℝ≥0∞))
    (fun _ => measurable_const) (fun _ => dependsOn_const 1)
    (by intro j; simp) (by intro j; simp)
    (by intro j; exact empty_subset _) (by intro j; simp)
    (by
      intro k hk
      refine ⟨fun _ _ => 1, fun _ => measurable_const, ?_, ?_⟩
      · intro i; simp
      · intro j; simp [lmarginal])
  simpa using H

-- Both coordinate and row types empty, retaining the empty active set.
example {X : Empty → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
      (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j : Empty, (fun _ : ∀ i, X i => (1 : ℝ≥0∞)) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => ∏ i ∈ (∅ : Finset Empty), h i (x i)) := by
  have H := exists_common_profiles_of_deleted_marginal_factorizations μ ∅
    (fun _ : Empty => ∅) (fun _ _ => (1 : ℝ≥0∞))
    (fun j => isEmptyElim j) (fun j => isEmptyElim j)
    (fun j => isEmptyElim j) (fun j => isEmptyElim j)
    (fun j => isEmptyElim j) (fun j => isEmptyElim j)
    (by intro k hk; simp at hk)
  simpa using H

-- Distinct nonempty proper supports, with every mass strictly positive and finite.
example {X : Fin 3 → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
      (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j : Fin 2, (fun _ : ∀ i, X i => (1 : ℝ≥0∞)) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => ∏ i ∈ ({j.castSucc} : Finset (Fin 3)), h i (x i)) := by
  have H := exists_common_profiles_of_deleted_marginal_factorizations μ
    (univ : Finset (Fin 3)) (fun j : Fin 2 => {j.castSucc}) (fun _ _ => (1 : ℝ≥0∞))
    (fun _ => measurable_const) (fun _ => dependsOn_const 1)
    (by intro j; simp) (by intro j; simp)
    (by intro j; exact subset_univ _)
    (by intro j he; have hh := congrArg Finset.card he; simp at hh)
    (by
      intro k hk
      refine ⟨fun _ _ => 1, fun _ => measurable_const, ?_, ?_⟩
      · intro i; simp
      · intro j; simp [lmarginal])
  simpa using H

#print axioms exists_common_profiles_of_deleted_marginal_factorizations
