/- GID: D5/S3/Topology/Measures/L1Restriction
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/L1Restriction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal measurable restrictions of real L1 classes and their exact norms. -/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Literal restrictions used by the raw-set subsequence splitting. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory

namespace D5.S3.Topology.Measures.L1Restriction

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The L1 class of the literal indicator restriction of the original class. -/
noncomputable def restrict (s : Set Ω) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) : Lp ℝ 1 μ :=
  (MemLp.indicator hs.nullMeasurableSet (Lp.memLp f)).toLp (s.indicator f)

theorem coe_restrict (s : Set Ω) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    ⇑(restrict s hs f) =ᵐ[μ] s.indicator f := MemLp.coeFn_toLp _

theorem norm_restrict (s : Set Ω) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    ‖restrict s hs f‖ = ∫ x in s, ‖f x‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, ‖s.indicator f x‖ ∂μ := integral_congr_ae ((coe_restrict s hs f).fun_comp norm)
    _ = ∫ x, s.indicator (fun x => ‖f x‖) x ∂μ := by
      congr 1; ext x; by_cases hx : x ∈ s <;> simp [hx]
    _ = _ := integral_indicator hs

theorem enorm_restrict (s : Set Ω) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    ‖restrict s hs f‖ₑ = ∫⁻ x in s, ‖f x‖ₑ ∂μ := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (coe_restrict s hs f),
    eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
    eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f).restrict]

theorem add_compl (s : Set Ω) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    restrict s hs f + restrict sᶜ hs.compl f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (restrict s hs f) (restrict sᶜ hs.compl f),
    coe_restrict s hs f, coe_restrict sᶜ hs.compl f] with x ha hb hc
  rw [ha, Pi.add_apply, hb, hc]
  by_cases hx : x ∈ s <;> simp [hx]

theorem norm_add_compl (s : Set Ω) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    ‖restrict s hs f‖ + ‖restrict sᶜ hs.compl f‖ = ‖f‖ := by
  rw [norm_restrict, norm_restrict, L1.norm_eq_integral_norm]
  exact integral_add_compl hs (memLp_one_iff_integrable.1 (Lp.memLp f)).norm

theorem norm_le (s : Set Ω) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    ‖restrict s hs f‖ ≤ ‖f‖ := by
  rw [← norm_add_compl s hs f]
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem norm_mono {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (f : Lp ℝ 1 μ) : ‖restrict s hs f‖ ≤ ‖restrict t ht f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coe_restrict s hs f, coe_restrict t ht f] with x hx hy
  rw [hx, hy]
  by_cases hxs : x ∈ s
  · simp [hxs, hst hxs]
  · simp [hxs]

/-- Actual measurable hard-tail set of the canonical representative. -/
def tailSet (k : ℕ) (f : Lp ℝ 1 μ) : Set Ω := {x | (k : ℝ) ≤ ‖f x‖}

theorem measurable_tailSet (k : ℕ) (f : Lp ℝ 1 μ) : MeasurableSet (tailSet k f) :=
  measurableSet_le measurable_const (Lp.stronglyMeasurable f).measurable.norm

/-- Real hard-tail mass. -/
noncomputable def tailNorm (k : ℕ) (f : Lp ℝ 1 μ) : ℝ :=
  ‖restrict (tailSet k f) (measurable_tailSet k f) f‖

theorem tailNorm_antitone (f : Lp ℝ 1 μ) : Antitone (fun k => tailNorm k f) := by
  intro k K hkK
  apply norm_mono (measurable_tailSet K f) (measurable_tailSet k f) _ f
  intro x hx
  exact (show (k : ℝ) ≤ K by exact_mod_cast hkK).trans hx

/-- Exact subtraction of nested hard tails for the literal low restriction. -/
theorem tailNorm_compl (f : Lp ℝ 1 μ) (k K : ℕ) (hk : 0 < k) (hkK : k ≤ K) :
    tailNorm k (restrict (tailSet K f)ᶜ (measurable_tailSet K f).compl f) =
      tailNorm k f - tailNorm K f := by
  let A := tailSet K f
  have hA : MeasurableSet A := measurable_tailSet K f
  let g := restrict Aᶜ hA.compl f
  let S := tailSet k f
  have hS : MeasurableSet S := measurable_tailSet k f
  have hAS : A ⊆ S := by
    intro x hx
    exact (show (k : ℝ) ≤ K by exact_mod_cast hkK).trans hx
  have heq : restrict (tailSet k g) (measurable_tailSet k g) g = restrict (S \ A) (hS.diff hA) f := by
    apply Lp.ext
    filter_upwards [coe_restrict (tailSet k g) (measurable_tailSet k g) g,
      coe_restrict Aᶜ hA.compl f, coe_restrict (S \ A) (hS.diff hA) f] with x hx hg hy
    rw [hx, hy]
    change (tailSet k g).indicator g x = (S \ A).indicator f x
    have hgx : g x = Aᶜ.indicator f x := hg
    by_cases hxa : x ∈ A
    · have hg0 : g x = 0 := by simpa [hxa] using hgx
      have hk0 : ¬ (k : ℝ) ≤ 0 := by exact_mod_cast (not_le.mpr hk)
      simp [tailSet, hg0, hk0, hxa]
    · have hgf : g x = f x := by simpa [hxa] using hgx
      by_cases hxs : x ∈ S
      · have hxg : x ∈ tailSet k g := by simpa only [tailSet, mem_setOf_eq, hgf] using (show (k : ℝ) ≤ ‖f x‖ from hxs)
        simp [hxg, hxs, hxa, hgf]
      · have hxg : x ∉ tailSet k g := by simpa only [tailSet, mem_setOf_eq, hgf] using (show ¬ (k : ℝ) ≤ ‖f x‖ from hxs)
        simp [hxg, hxs, hxa]
  change ‖restrict (tailSet k g) (measurable_tailSet k g) g‖ = _
  rw [heq, norm_restrict]
  change _ = ‖restrict S hS f‖ - ‖restrict A hA f‖
  rw [norm_restrict, norm_restrict]
  exact setIntegral_sdiff hA (memLp_one_iff_integrable.1 (Lp.memLp f)).norm.integrableOn hAS

end D5.S3.Topology.Measures.L1Restriction
