/- GID: D5/S3/Analytic/Convexity/MeasurableFiniteMoments
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/MeasurableFiniteMoments
   mirror-E: none(waiver:finite-dimensional-moment-proof)
   anchors: []
   utility: none
   digest: Exact finite point evaluations for integrable finite-dimensional moments. -/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! The actual-hull step in finite moment cubature. The argument uses supporting
hyperplanes and dimension descent, without closedness or compactness of the image.
Mathematical reference: Bayer and Teichmann, The proof of Tchakaloff's theorem,
math/0502473v2, Corollary 2 and Remark 2, DOI 10.1090/S0002-9939-06-08249-9. -/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

namespace D5.S3.Analytic.Convexity.MeasurableFiniteMoments

private theorem zero_mem_convexHull_of_integral_zero_aux (d : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E], Module.finrank ℝ E = d →
    ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      (f : α → E), Integrable f μ → (∫ a, f a ∂μ) = 0 →
        (0 : E) ∈ convexHull ℝ (range f) := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro E _ _ _ hd α _ μ _ f hfi hf0
    have descend (P : Submodule ℝ E) (hP : P ≠ ⊤)
        (g : α → P) (hg : (fun a => (g a : E)) =ᵐ[μ] f)
        (hr : range (fun a => (g a : E)) ⊆ range f) :
        (0 : E) ∈ convexHull ℝ (range f) := by
      have hgi : Integrable g μ := by
        apply (isometry_subtype_coe.lipschitz.integrable_comp_iff_of_antilipschitz
          isometry_subtype_coe.antilipschitz (show ((0 : P) : E) = 0 from rfl)).mp
        exact hfi.congr hg.symm
      have hg0 : (∫ a, g a ∂μ) = 0 := by
        apply Subtype.val_injective
        change P.subtypeL (∫ a, g a ∂μ) = P.subtypeL 0
        rw [← P.subtypeL.integral_comp_comm hgi]
        change (∫ a, (g a : E) ∂μ) = 0
        rw [integral_congr_ae hg, hf0]
      have hdim : Module.finrank ℝ P < d := hd ▸ Submodule.finrank_lt hP
      have hmem := ih (Module.finrank ℝ P) hdim rfl μ g hgi hg0
      have him : (0 : E) ∈ P.subtype '' convexHull ℝ (range g) :=
        ⟨0, hmem, rfl⟩
      rw [P.subtype.image_convexHull, ← range_comp] at him
      exact convexHull_mono hr him
    let P := Submodule.span ℝ (range f)
    by_cases hP : P = ⊤
    · have haff0 : (0 : E) ∈ affineSpan ℝ (range f) := by
        rw [← hf0]
        exact (affineSpan ℝ (range f)).convex.integral_mem
          (affineSpan ℝ (range f)).closed_of_finiteDimensional
          (Eventually.of_forall fun a => subset_affineSpan ℝ _ (mem_range_self a)) hfi
      have haff : affineSpan ℝ (range f) = ⊤ := by
        rw [affineSpan_eq_span_of_zero_mem haff0]
        exact congrArg Submodule.toAffineSubspace hP
      have hint : (interior (convexHull ℝ (range f))).Nonempty := by
        apply (convex_convexHull ℝ (range f)).interior_nonempty_iff_affineSpan_eq_top.mpr
        rwa [affineSpan_convexHull]
      by_contra hnot
      obtain ⟨l, hl, hle⟩ := geometric_hahn_banach_of_nonempty_interior_point
        (convex_convexHull ℝ (range f)) (fun h => hnot (interior_subset h)) hint
      have hnonpos : ∀ a, l (f a) ≤ 0 := by
        intro a
        simpa using hle (f a) (subset_convexHull ℝ _ (mem_range_self a))
      have hli := l.integrable_comp hfi
      have hneg0 : (∫ a, -(l (f a)) ∂μ) = 0 := by
        rw [integral_neg, l.integral_comp_comm hfi, hf0, map_zero, neg_zero]
      have hzero : ∀ᵐ a ∂μ, l (f a) = 0 := by
        have hz := (integral_eq_zero_iff_of_nonneg
          (fun a => neg_nonneg.mpr (hnonpos a)) hli.neg).mp hneg0
        filter_upwards [hz] with a ha
        exact neg_eq_zero.mp ha
      obtain ⟨a₀, ha₀⟩ := hzero.exists
      let Q := l.toLinearMap.ker
      have hQ : Q ≠ ⊤ := by
        intro h
        apply hl
        ext x
        exact (LinearMap.mem_ker.mp (h ▸ Submodule.mem_top : x ∈ Q))
      let g : α → Q := fun a =>
        if ha : l (f a) = 0 then ⟨f a, ha⟩ else ⟨f a₀, ha₀⟩
      apply hnot
      apply descend Q hQ g
      · filter_upwards [hzero] with a ha
        simp [g, ha]
      · rintro _ ⟨a, rfl⟩
        by_cases ha : l (f a) = 0
        · exact ⟨a, by simp [g, ha]⟩
        · exact ⟨a₀, by simp [g, ha]⟩
    · let g : α → P := fun a => ⟨f a, Submodule.subset_span (mem_range_self a)⟩
      exact descend P hP g (Eventually.of_forall fun _ => rfl) (by rfl)

/-- A probability barycenter of integrable finite-dimensional moments belongs to
the actual convex hull of their point values, without an image-closedness premise. -/
theorem integral_mem_convexHull {E α : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → E} (hfi : Integrable f μ) :
    (∫ a, f a ∂μ) ∈ convexHull ℝ (range f) := by
  let b := ∫ a, f a ∂μ
  let g := fun a => f a - b
  have hgi : Integrable g μ := hfi.sub (integrable_const b)
  have hg0 : (∫ a, g a ∂μ) = 0 := by simp [g, integral_sub hfi (integrable_const b), b]
  have hmem := zero_mem_convexHull_of_integral_zero_aux
    (Module.finrank ℝ E) rfl μ g hgi hg0
  let T : E →ᵃ[ℝ] E := (AffineEquiv.constVAdd ℝ E b).toAffineMap
  have him : T 0 ∈ T '' convexHull ℝ (range g) := ⟨0, hmem, rfl⟩
  rw [T.image_convexHull, ← range_comp] at him
  have he : T ∘ g = f := by ext a; simp [T, g]
  rw [he] at him
  simpa [T, b] using him

/-- The selected point evaluations can be required to lie in any conull set.
In particular, infinities on a null set need never be converted to real moments. -/
theorem finite_moments_probability {E α : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → E} (hfi : Integrable f μ)
    {s : Set α} (hs : ∀ᵐ a ∂μ, a ∈ s) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (a : Fin k → α),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, a i ∈ s) ∧
        ∑ i, w i • f (a i) = ∫ a, f a ∂μ := by
  classical
  obtain ⟨a₀, ha₀⟩ := hs.exists
  let g : α → E := fun a => if a ∈ s then f a else f a₀
  have hgf : g =ᵐ[μ] f := hs.mono fun a ha => by simp [g, ha]
  have hgi := hfi.congr hgf.symm
  have hmem : (∫ a, f a ∂μ) ∈ convexHull ℝ (f '' s) := by
    rw [← integral_congr_ae hgf]
    apply convexHull_mono (t := f '' s) ?_ (integral_mem_convexHull μ hgi)
    rintro _ ⟨a, rfl⟩
    by_cases ha : a ∈ s
    · exact ⟨a, ha, by simp [g, ha]⟩
    · exact ⟨a₀, ha₀, by simp [g, ha]⟩
  obtain ⟨ι, hi, w, z, hw, hw1, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp hmem
  choose a ha haz using hz
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, w ∘ e, a ∘ e, fun i => hw (e i), ?_,
    fun i => ha (e i), ?_⟩
  · simpa [Function.comp_def] using (e.sum_comp w).trans hw1
  · simpa [Function.comp_def, haz] using (e.sum_comp (fun i => w i • z i)).trans he

/-- Exact cubature for a finite measure, with no positivity or compactness
assumption on the real moments and with the zero measure represented by no labels. -/
theorem finite_moments {E α : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → E} (hfi : Integrable f μ)
    {s : Set α} (hs : ∀ᵐ a ∂μ, a ∈ s) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (a : Fin k → α),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = μ.real univ) ∧ (∀ i, a i ∈ s) ∧
        ∑ i, w i • f (a i) = ∫ a, f a ∂μ := by
  classical
  by_cases hμ : μ = 0
  · subst μ
    exact ⟨0, Fin.elim0, Fin.elim0, by simp, by simp, by simp, by simp⟩
  letI : NeZero μ := ⟨hμ⟩
  let ν := (μ univ)⁻¹ • μ
  obtain ⟨k, w, a, hw, hw1, ha, he⟩ := finite_moments_probability ν
    hfi.to_average (hs.filter_mono (Measure.ae_mono' smul_absolutelyContinuous))
  refine ⟨k, fun i => μ.real univ * w i, a,
    fun i => mul_nonneg ENNReal.toReal_nonneg (hw i), ?_, ha, ?_⟩
  · rw [← Finset.mul_sum, hw1, mul_one]
  · simp_rw [mul_smul]
    rw [← Finset.smul_sum, he]
    exact measure_smul_average μ f

#print axioms integral_mem_convexHull
#print axioms finite_moments

end D5.S3.Analytic.Convexity.MeasurableFiniteMoments
