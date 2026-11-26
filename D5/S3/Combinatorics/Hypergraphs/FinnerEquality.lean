/- GID: D5/S3/Combinatorics/Hypergraphs/FinnerEquality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hypergraphs/FinnerEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common coordinate profiles for balanced Finner saturation. -/

module

public import D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure
public import D5.S3.Analytic.Measure.NormalizedHolderEquality
import D5.S3.Analytic.Measure.ProductSupportIntersection
import Mathlib.Probability.Independence.Integration

/-! # Balanced Finner equality and canonical coordinate marginals -/

@[expose] public section

open MeasureTheory Function Finset Filter ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Hypergraphs.FinnerEquality

variable {I : Type*} [Fintype I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

private lemma marginal_fixed [DecidableEq I] (u : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} {S : Set I} (hd : DependsOn f S)
    (hu : Disjoint S (u : Set I)) : lmarginal μ u f = f := by
  ext x
  have hc (y : ∀ i : u, X i) : f (updateFinset x u y) = f x := by
    apply hd
    intro i hi
    have hni : i ∉ u := fun h => Set.disjoint_left.mp hu hi h
    simp [updateFinset, hni]
  change (∫⁻ y : ∀ i : u, X i, f (updateFinset x u y)
    ∂MeasureTheory.Measure.pi (fun i : u => μ i)) = f x
  simp_rw [hc]
  simp

private lemma marginal_idem [DecidableEq I] (u : Finset I)
    (f : (∀ i, X i) → ℝ≥0∞) :
    lmarginal μ u (lmarginal μ u f) = lmarginal μ u f := by
  apply marginal_fixed
  · intro x y hxy
    exact lmarginal_congr μ f hxy
  · exact disjoint_compl_left

private lemma integral_marginal [DecidableEq I] (u : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, lmarginal μ u f x ∂MeasureTheory.Measure.pi μ) =
      ∫⁻ x, f x ∂MeasureTheory.Measure.pi μ :=
  lintegral_eq_of_lmarginal_eq u (hf.lmarginal μ) hf (marginal_idem μ u f)

private lemma marginal_absorb_singleton [DecidableEq I] (u : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) {k : I} (hk : k ∈ u) :
    lmarginal μ u (lmarginal μ {k} f) = lmarginal μ u f := by
  conv_lhs => rw [← insert_erase hk,
    lmarginal_insert' _ (hf.lmarginal μ) (notMem_erase k u)]
  conv_rhs => rw [← insert_erase hk, lmarginal_insert' _ hf (notMem_erase k u)]
  change lmarginal μ (u.erase k) (lmarginal μ {k} (lmarginal μ {k} f)) =
    lmarginal μ (u.erase k) (lmarginal μ {k} f)
  rw [marginal_idem]

private lemma integral_coordinate_product (s : Finset I) (h : ∀ i, X i → ℝ≥0∞)
    (hm : ∀ i, Measurable (h i)) :
    (∫⁻ x, ∏ i ∈ s, h i (x i) ∂MeasureTheory.Measure.pi μ) =
      ∏ i ∈ s, ∫⁻ t, h i t ∂μ i := by
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun s _
    (iIndepFun_pi (fun i => (hm i).aemeasurable))
    (fun i => (hm i).comp (measurable_pi_apply i))]
  apply prod_congr rfl
  intro i _
  exact (measurePreserving_eval μ i).lintegral_comp (hm i).aemeasurable

end D5.S3.Combinatorics.Hypergraphs.FinnerEquality
