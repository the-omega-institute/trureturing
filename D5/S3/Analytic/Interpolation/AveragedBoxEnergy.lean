/- GID: D5/S3/Analytic/Interpolation/AveragedBoxEnergy
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/AveragedBoxEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform averaged box energy captures every separated complex jump. -/

import D5.S3.Analytic.Interpolation.SeparatedJumpRectangles
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
The prefix itself may have nonzero limits at infinity. Only its difference,
restricted to a bounded-width strip, is integrated. No whole-line integral
of the prefix is split off. Half-open boxes make the prefix identity exact.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace D5.S3.Analytic.Interpolation.AveragedBoxEnergy

open D5.S3.Analytic.Interpolation.SeparatedJumpRectangles

variable {ι : Type*} [Fintype ι]

/-- Half-open boxes; replacing them by closed boxes changes no energy integral. -/
def boxSum (x : ι → ℝ) (c : ι → ℂ) (s u : ℝ) : ℂ :=
  ∑ i, (Ico (x i) (x i + s)).indicator (fun _ => c i) u

private lemma boxSum_eq_prefix (x : ι → ℝ) (c : ι → ℂ) {s : ℝ} (hs : 0 ≤ s)
    (u : ℝ) : boxSum x c s u = prefix x c u - prefix x c (u - s) := by
  classical
  rw [boxSum, prefix, prefix, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ≤ u
  · by_cases hi' : x i ≤ u - s
    · have hn : u ∉ Ico (x i) (x i + s) := by
        intro hu
        linarith [hu.2]
      simp [hi, hi', hn]
    · have hm : u ∈ Ico (x i) (x i + s) := ⟨hi, by linarith⟩
      simp [hi, hi', hm]
  · have hi' : ¬ x i ≤ u - s := by linarith
    have hn : u ∉ Ico (x i) (x i + s) := fun hu => hi hu.1
    simp [hi, hi', hn]

private def differenceEnergy (x : ι → ℝ) (c : ι → ℂ) (p : ℝ × ℝ) : ℝ :=
  Complex.normSq (prefix x c p.1 - prefix x c p.2)

private def widthStrip (a : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 2 * a}

private lemma measurable_differenceEnergy (x : ι → ℝ) (c : ι → ℂ) :
    Measurable (differenceEnergy x c) :=
  Complex.continuous_normSq.measurable.comp
    (((measurable_prefix x c).comp measurable_fst).sub
      ((measurable_prefix x c).comp measurable_snd))

private lemma measurable_widthStrip (a : ℝ) : MeasurableSet (widthStrip a) := by
  exact (measurableSet_Icc.preimage (measurable_fst.sub measurable_snd))

private lemma differenceEnergy_bound (x : ι → ℝ) (c : ι → ℂ) (p : ℝ × ℝ) :
    ‖differenceEnergy x c p‖ ≤ (2 * ∑ i, ‖c i‖) ^ 2 := by
  have hc : 0 ≤ ∑ i, ‖c i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (c i))
  have h := (norm_sub_le (prefix x c p.1) (prefix x c p.2)).trans
    (add_le_add (norm_prefix_le x c p.1) (norm_prefix_le x c p.2))
  rw [differenceEnergy, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (prefix x c p.1 - prefix x c p.2)]

/-- Coordinates from the strip to width and upper endpoint. -/
private def stripCoordinates : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.1 - p.2, p.1)
  invFun p := (p.2, p.2 - p.1)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  measurable_toFun := (measurable_fst.sub measurable_snd).prodMk measurable_fst
  measurable_invFun := measurable_snd.prodMk (measurable_snd.sub measurable_fst)

private lemma stripCoordinates_preserving :
    MeasurePreserving stripCoordinates (volume.prod volume) (volume.prod volume) := by
  have h := (measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).comp
      (((MeasurePreserving.id (volume : Measure ℝ)).prod
        (measurePreserving_neg (volume : Measure ℝ))).comp
          (measurePreserving_prod_sub (volume : Measure ℝ) (volume : Measure ℝ)))
  convert h using 1
  ext p <;> simp [stripCoordinates, Function.comp_def, Prod.map, neg_sub]

private def widthEnergy (x : ι → ℝ) (c : ι → ℂ) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Icc a (2 * a)).indicator
    (fun s => Complex.normSq (prefix x c p.2 - prefix x c (p.2 - s))) p.1

private lemma widthEnergy_measurable (x : ι → ℝ) (c : ι → ℂ) (a : ℝ) :
    Measurable (widthEnergy x c a) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      Complex.normSq (prefix x c p.2 - prefix x c (p.2 - p.1))) :=
    Complex.continuous_normSq.measurable.comp
      (((measurable_prefix x c).comp measurable_snd).sub
        ((measurable_prefix x c).comp (measurable_snd.sub measurable_fst)))
  convert hm.indicator (measurableSet_Icc.preimage measurable_fst) using 1

private lemma widthEnergy_integrable (x : ι → ℝ) (c : ι → ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (widthEnergy x c a) (volume.prod volume) := by
  classical
  let B : ℝ := ∑ i, |x i|
  let R : ℝ := B + 2 * a + 1
  let C : Set (ℝ × ℝ) := Icc a (2 * a) ×ˢ Icc (-R) R
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
  have hx (i : ι) : |x i| ≤ B := by
    exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  have hmeas : MeasurableSet C := measurableSet_Icc.prod measurableSet_Icc
  have hfinite : (volume.prod volume) C ≠ ⊤ := by
    simp [C, Measure.prod_prod, Real.volume_Icc, ENNReal.mul_ne_top]
  have hbound (p : ℝ × ℝ) : ‖widthEnergy x c a p‖ ≤ (2 * ∑ i, ‖c i‖) ^ 2 := by
    by_cases hp : p.1 ∈ Icc a (2 * a)
    · simpa [widthEnergy, hp, differenceEnergy] using
        differenceEnergy_bound x c (p.2, p.2 - p.1)
    · simp [widthEnergy, hp]
  have hi : IntegrableOn (widthEnergy x c a) C (volume.prod volume) :=
    Measure.integrableOn_of_bounded hfinite (widthEnergy_measurable x c a).aestronglyMeasurable
      (ae_of_all _ hbound)
  have he : C.indicator (widthEnergy x c a) = widthEnergy x c a := by
    funext p
    by_cases hp : p ∈ C
    · exact indicator_of_mem hp _
    · rw [indicator_of_notMem hp]
      by_cases hs : p.1 ∈ Icc a (2 * a)
      · have hu : p.2 ∉ Icc (-R) R := fun hu => hp ⟨hs, hu⟩
        have hz : prefix x c p.2 = prefix x c (p.2 - p.1) := by
          unfold prefix
          apply Finset.sum_congr rfl
          intro i _
          have hxi := (abs_le.mp (hx i))
          rcases not_and_or.mp hu with hlow | hhigh
          · have hl : p.2 < -R := lt_of_not_ge hlow
            have h1 : ¬ x i ≤ p.2 := by dsimp [R] at hl; linarith [hxi.1]
            have h2 : ¬ x i ≤ p.2 - p.1 := by dsimp [R] at hl; linarith [hxi.1, hs.1]
            simp [h1, h2]
          · have hh : R < p.2 := lt_of_not_ge hhigh
            have h1 : x i ≤ p.2 := by dsimp [R] at hh; linarith [hxi.2]
            have h2 : x i ≤ p.2 - p.1 := by dsimp [R] at hh; linarith [hxi.2, hs.2]
            simp [h1, h2]
        simp [widthEnergy, hs, hz]
      · simp [widthEnergy, hs]
  rw [← he]
  exact (integrable_indicator_iff hmeas).mpr hi

private lemma strip_integrable (x : ι → ℝ) (c : ι → ℂ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (differenceEnergy x c) (widthStrip a) (volume.prod volume) := by
  have he : (widthStrip a).indicator (differenceEnergy x c) =
      widthEnergy x c a ∘ stripCoordinates := by
    funext p
    simp only [Function.comp_def, widthEnergy, stripCoordinates, widthStrip, differenceEnergy]
    by_cases hp : a ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 2 * a <;>
      simp [hp, sub_sub_cancel]
  apply (integrable_indicator_iff (measurable_widthStrip a)).mp
  rw [he]
  exact stripCoordinates_preserving.integrable_comp_of_integrable
    (widthEnergy_integrable x c ha)

private lemma strip_integral_eq_average (x : ι → ℝ) (c : ι → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ p in widthStrip a, differenceEnergy x c p ∂volume.prod volume) =
      ∫ s : ℝ in Icc a (2 * a), ∫ u : ℝ, Complex.normSq (boxSum x c s u) := by
  rw [← integral_indicator (measurable_widthStrip a)]
  have he : (widthStrip a).indicator (differenceEnergy x c) =
      widthEnergy x c a ∘ stripCoordinates := by
    funext p
    by_cases hp : p ∈ widthStrip a
    · simp [widthEnergy, stripCoordinates, widthStrip, differenceEnergy] at hp ⊢
      simp [hp, sub_sub_cancel]
    · simp [widthEnergy, stripCoordinates, widthStrip, differenceEnergy] at hp ⊢
      simp [hp]
  rw [he, stripCoordinates_preserving.integral_comp stripCoordinates.measurableEmbedding,
    integral_prod _ (widthEnergy_integrable x c ha)]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply ae_of_all
  intro s
  by_cases hs : s ∈ Icc a (2 * a)
  · simp only [widthEnergy, indicator_of_mem hs]
    congr 1
    funext u
    rw [boxSum_eq_prefix x c (ha.le.trans hs.1)]
  · simp [widthEnergy, hs]

/-- All separated jumps are captured in every dyadic-width averaging band. -/
theorem averaged_box_energy_lower_bound (x : ι → ℝ) (c : ι → ℂ) {g a : ℝ}
    (hg : 0 < g) (hga : g ≤ a)
    (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|) :
    a * g / 16 * (∑ i, Complex.normSq (c i)) ≤
      ∫ s : ℝ in Icc a (2 * a), ∫ u : ℝ, Complex.normSq (boxSum x c s u) := by
  classical
  let R : ι → Set (ℝ × ℝ) := fun i => nodeWindow x g i ×ˢ baseWindow x a i
  have ha : 0 < a := hg.trans_le hga
  have hsub (i : ι) : R i ⊆ widthStrip a := rect_subset_strip x hg hga i
  have hi := strip_integrable x c ha
  have hiR (i : ι) : IntegrableOn (differenceEnergy x c) (R i) (volume.prod volume) :=
    hi.mono_set (hsub i)
  have hRmeas (i : ι) : MeasurableSet (R i) := measurableSet_Ico.prod measurableSet_Icc
  have hdis : Pairwise (Disjoint on R) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (window_disjoint x hg hsep hij) hp.1 hq.1
  have hlower (i : ι) : a * g / 16 * Complex.normSq (c i) ≤
      ∫ p in R i, differenceEnergy x c p ∂volume.prod volume := by
    have his : Integrable (fun p : ℝ × ℝ => differenceEnergy x c p)
        ((volume.restrict (nodeWindow x g i)).prod (volume.restrict (baseWindow x a i))) := by
      simpa only [Measure.prod_restrict] using hiR i
    rw [setIntegral_prod _ (hiR i), integral_integral_swap his]
    have hm := integral_mono_ae
      (integrableOn_const (by simp) : IntegrableOn
        (fun _ : ℝ => g / 8 * Complex.normSq (c i)) (baseWindow x a i))
      his.swap.integral_prod_left
      (ae_of_all _ (fun v => node_window_energy_lower_bound x c hg hsep i v))
    have hv : (∫ v : ℝ in baseWindow x a i, g / 8 * Complex.normSq (c i)) =
        a * g / 16 * Complex.normSq (c i) := by
      rw [baseWindow, setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
      ring
    exact hv ▸ hm
  calc
    a * g / 16 * (∑ i, Complex.normSq (c i)) =
        ∑ i, a * g / 16 * Complex.normSq (c i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i, ∫ p in R i, differenceEnergy x c p ∂volume.prod volume :=
      Finset.sum_le_sum (fun i _ => hlower i)
    _ = ∫ p in ⋃ i, R i, differenceEnergy x c p ∂volume.prod volume :=
      (integral_iUnion_fintype hRmeas hdis hiR).symm
    _ ≤ ∫ p in widthStrip a, differenceEnergy x c p ∂volume.prod volume :=
      setIntegral_mono_set hi (ae_of_all _ (fun p => Complex.normSq_nonneg _))
        (ae_of_all _ (iUnion_subset hsub))
    _ = _ := strip_integral_eq_average x c ha

#print axioms averaged_box_energy_lower_bound

end D5.S3.Analytic.Interpolation.AveragedBoxEnergy
