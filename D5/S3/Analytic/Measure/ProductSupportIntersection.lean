/- GID: D5/S3/Analytic/Measure/ProductSupportIntersection
   generality: G
   mirror-B: D5/B/S3/Analytic/Measure/ProductSupportIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common measurable representatives on intersections of coordinate supports. -/

module

public import OmegaBuild.Commands
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.Logic.Function.DependsOn

compile_only_with_mathlib

/-! # Intersections of coordinate supports under product probability laws

Almost-everywhere equal measurable nonnegative functions admit a measurable common
representative on the intersection of their coordinate supports.
-/

@[expose] public section

open MeasureTheory Function Filter
open scoped ENNReal

noncomputable section
set_option autoImplicit false

namespace D5.S3.Analytic.Measure.ProductSupportIntersection

variable {I : Type*} [Fintype I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

lemma marginal_congr_ae [DecidableEq I] (s : Finset I) {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (he : f =ᵐ[MeasureTheory.Measure.pi μ] g) :
    lmarginal μ s f =ᵐ[MeasureTheory.Measure.pi μ] lmarginal μ s g := by
  classical
  let e : (∀ i, X i) → ℝ≥0∞ := fun x => if f x = g x then 0 else 1
  have hme : Measurable e := Measurable.ite (measurableSet_eq_fun hf hg)
    measurable_const measurable_const
  have he0 : ∫⁻ x, e x ∂MeasureTheory.Measure.pi μ = 0 := by
    apply (lintegral_eq_zero_iff hme).2
    filter_upwards [he] with x hx
    simp [e, hx]
  have hid : lmarginal μ s (lmarginal μ s e) = lmarginal μ s e := by
    ext x
    change (∫⁻ y, lmarginal μ s e (updateFinset x s y)
      ∂MeasureTheory.Measure.pi (fun i : s => μ i)) = _
    have hc : ∀ y, lmarginal μ s e (updateFinset x s y) = lmarginal μ s e x := by
      intro y
      apply lmarginal_congr μ e
      intro i hi
      simp [updateFinset, hi]
    simp_rw [hc]
    simp
  have hzero : lmarginal μ s e =ᵐ[MeasureTheory.Measure.pi μ] 0 := by
    apply (lintegral_eq_zero_iff (hme.lmarginal μ)).1
    rw [lintegral_eq_of_lmarginal_eq s (hme.lmarginal μ) hme hid, he0]
  filter_upwards [hzero] with x hx
  have hslice : (fun y : ∀ i : s, X i => e (updateFinset x s y))
      =ᵐ[MeasureTheory.Measure.pi (fun i : s => μ i)] 0 := by
    apply (lintegral_eq_zero_iff (hme.comp measurable_updateFinset)).1
    exact hx
  apply lintegral_congr_ae
  filter_upwards [hslice] with y hy
  by_contra hne
  simp [e, hne] at hy

omit [Fintype I] [∀ i, IsProbabilityMeasure (μ i)] in
lemma marginal_depends [DecidableEq I] (u : Finset I) {f : (∀ i, X i) → ℝ≥0∞}
    {S : Set I} (hd : DependsOn f S) : DependsOn (lmarginal μ u f) (S \ u) := by
  classical
  intro x y hxy
  apply lintegral_congr
  intro z
  exact hd.updateFinset z hxy

/-- Under a finite product probability law, coordinate supports of measurable
almost-everywhere equal ENNReal functions can be intersected. -/
theorem exists_measurable_intersection_representative
    {f g : (∀ i, X i) → ℝ≥0∞} (S T : Set I)
    (hf : Measurable f) (hg : Measurable g)
    (hSf : DependsOn f S) (hTg : DependsOn g T)
    (he : f =ᵐ[MeasureTheory.Measure.pi μ] g) :
    ∃ h : (∀ i, X i) → ℝ≥0∞, Measurable h ∧ DependsOn h (S ∩ T) ∧
      h =ᵐ[MeasureTheory.Measure.pi μ] f ∧ h =ᵐ[MeasureTheory.Measure.pi μ] g := by
  classical
  let u : Finset I := Sᶜ.toFinset
  have hfix : lmarginal μ u f = f := by
    ext x
    have hc : ∀ y : ∀ i : u, X i, f (updateFinset x u y) = f x := by
      intro y
      apply hSf
      intro i hi
      have hni : i ∉ u := by simpa [u] using hi
      simp [updateFinset, hni]
    change (∫⁻ y : ∀ i : u, X i, f (updateFinset x u y)
      ∂MeasureTheory.Measure.pi (fun i : u => μ i)) = f x
    simp_rw [hc]
    simp
  have hae : lmarginal μ u g =ᵐ[MeasureTheory.Measure.pi μ] f := by
    simpa only [hfix] using (marginal_congr_ae μ u hf hg he).symm
  refine ⟨lmarginal μ u g, hg.lmarginal μ, ?_, hae, hae.trans he⟩
  have hd := marginal_depends μ u hTg
  have hs : T \ (u : Set I) = S ∩ T := by
    ext i
    simp [u, and_comm]
  rwa [hs] at hd

end D5.S3.Analytic.Measure.ProductSupportIntersection
