/- GID: D5/S3/Analytic/Interpolation/AveragedBoxEnergy
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/AveragedBoxEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform averaged box energy captures every separated complex jump. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
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

variable {ι : Type*} [Fintype ι]

/-- The finite prefix, without any hypothesis on the total mass. -/
private def prefix (x : ι → ℝ) (c : ι → ℂ) (u : ℝ) : ℂ :=
  ∑ i, if x i ≤ u then c i else 0

/-- A half-open neighborhood divided into equal halves by its jump. -/
private def nodeWindow (x : ι → ℝ) (g : ℝ) (i : ι) : Set ℝ :=
  Ico (x i - g / 4) (x i + g / 4)

/-- The interval of earlier prefix observations paired with a jump neighborhood. -/
private def baseWindow (x : ι → ℝ) (a : ℝ) (i : ι) : Set ℝ :=
  Icc (x i - 7 * a / 4) (x i - 5 * a / 4)

private theorem measurable_prefix (x : ι → ℝ) (c : ι → ℂ) : Measurable (prefix x c) := by
  classical
  unfold prefix
  apply Finset.measurable_sum
  intro i _
  simpa only [Set.indicator, mem_Ici] using
    (measurable_const : Measurable (fun _ : ℝ => c i)).indicator measurableSet_Ici

private theorem norm_prefix_le (x : ι → ℝ) (c : ι → ℂ) (u : ℝ) :
    ‖prefix x c u‖ ≤ ∑ i, ‖c i‖ := by
  classical
  unfold prefix
  calc
    ‖∑ i, if x i ≤ u then c i else 0‖ ≤ ∑ i, ‖if x i ≤ u then c i else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp

private def otherPrefix (x : ι → ℝ) (c : ι → ℂ) (i : ι) : ℂ := by
  classical
  exact ∑ j ∈ Finset.univ.erase i, if x j ≤ x i then c j else 0

private theorem node_comparison (x : ι → ℝ) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|)
    (i j : ι) (hji : j ≠ i) {u : ℝ} (hu : u ∈ nodeWindow x g i) :
    x j ≤ u ↔ x j ≤ x i := by
  have hs := hsep j i hji
  change x i - g / 4 ≤ u ∧ u < x i + g / 4 at hu
  constructor
  · intro hju
    by_contra hji'
    have hlt : x i < x j := lt_of_not_ge hji'
    rw [abs_of_pos (sub_pos.mpr hlt)] at hs
    linarith [hu.2]
  · intro hji'
    rw [abs_of_nonpos (sub_nonpos.mpr hji')] at hs
    linarith [hu.1]

private theorem prefix_on_window (x : ι → ℝ) (c : ι → ℂ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|)
    (i : ι) {u : ℝ} (hu : u ∈ nodeWindow x g i) :
    prefix x c u = otherPrefix x c i + if x i ≤ u then c i else 0 := by
  classical
  calc
    prefix x c u = (∑ j ∈ Finset.univ.erase i, if x j ≤ u then c j else 0) +
        (if x i ≤ u then c i else 0) :=
      (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)).symm
    _ = otherPrefix x c i + if x i ≤ u then c i else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [node_comparison x hg hsep i j (Finset.mem_erase.mp hj).1 hu]

private theorem prefix_on_left (x : ι → ℝ) (c : ι → ℂ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|)
    (i : ι) {u : ℝ} (hu : u ∈ Ico (x i - g / 4) (x i)) :
    prefix x c u = otherPrefix x c i := by
  have hu' : u ∈ nodeWindow x g i := ⟨hu.1, by linarith [hu.2]⟩
  rw [prefix_on_window x c hg hsep i hu', if_neg (not_le.mpr hu.2), add_zero]

private theorem prefix_on_right (x : ι → ℝ) (c : ι → ℂ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|)
    (i : ι) {u : ℝ} (hu : u ∈ Ico (x i) (x i + g / 4)) :
    prefix x c u = otherPrefix x c i + c i := by
  have hu' : u ∈ nodeWindow x g i := ⟨by linarith [hu.1], hu.2⟩
  rw [prefix_on_window x c hg hsep i hu', if_pos hu.1]

private theorem two_point_square (A z : ℂ) :
    Complex.normSq z / 2 ≤ Complex.normSq A + Complex.normSq (A + z) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (2 * A.re + z.re), sq_nonneg (2 * A.im + z.im)]

/-- Each jump is captured uniformly, independently of the preceding prefix value. -/
private theorem node_window_energy_lower_bound (x : ι → ℝ) (c : ι → ℂ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|) (i : ι) (v : ℝ) :
    g / 8 * Complex.normSq (c i) ≤
      ∫ u : ℝ in nodeWindow x g i, Complex.normSq (prefix x c u - prefix x c v) := by
  let A := otherPrefix x c i - prefix x c v
  let f : ℝ → ℝ := fun u => Complex.normSq (prefix x c u - prefix x c v)
  have hleft : EqOn f (fun _ => Complex.normSq A) (Ico (x i - g / 4) (x i)) := by
    intro u hu
    dsimp only [f, A]
    rw [prefix_on_left x c hg hsep i hu]
  have hright : EqOn f (fun _ => Complex.normSq (A + c i))
      (Ico (x i) (x i + g / 4)) := by
    intro u hu
    dsimp only [f, A]
    rw [prefix_on_right x c hg hsep i hu]
    congr 1
    ring
  have hiL : IntegrableOn f (Ico (x i - g / 4) (x i)) := by
    apply (integrableOn_const (by simp) :
      IntegrableOn (fun _ : ℝ => Complex.normSq A) (Ico (x i - g / 4) (x i))).congr_fun
      (fun u hu => (hleft hu).symm) measurableSet_Ico
  have hiR : IntegrableOn f (Ico (x i) (x i + g / 4)) := by
    apply (integrableOn_const (by simp) :
      IntegrableOn (fun _ : ℝ => Complex.normSq (A + c i))
        (Ico (x i) (x i + g / 4))).congr_fun
      (fun u hu => (hright hu).symm) measurableSet_Ico
  have hdis : Disjoint (Ico (x i - g / 4) (x i)) (Ico (x i) (x i + g / 4)) := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    exact (not_lt_of_ge hv.1) hu.2
  have hsplit : nodeWindow x g i =
      Ico (x i - g / 4) (x i) ∪ Ico (x i) (x i + g / 4) := by
    exact (Ico_union_Ico_eq_Ico (by linarith) (by linarith)).symm
  have hvalL : (∫ u : ℝ in Ico (x i - g / 4) (x i), f u) =
      (g / 4) * Complex.normSq A := by
    rw [setIntegral_congr_fun measurableSet_Ico hleft, setIntegral_const,
      Real.volume_real_Ico_of_le (by linarith), smul_eq_mul]
    ring
  have hvalR : (∫ u : ℝ in Ico (x i) (x i + g / 4), f u) =
      (g / 4) * Complex.normSq (A + c i) := by
    rw [setIntegral_congr_fun measurableSet_Ico hright, setIntegral_const,
      Real.volume_real_Ico_of_le (by linarith), smul_eq_mul]
    ring
  change g / 8 * Complex.normSq (c i) ≤ ∫ u : ℝ in nodeWindow x g i, f u
  rw [hsplit, setIntegral_union hdis measurableSet_Ico hiL hiR, hvalL, hvalR]
  have htwo := mul_le_mul_of_nonneg_left (two_point_square A (c i)) (by linarith : 0 ≤ g / 4)
  nlinarith

/-- The jump neighborhoods of separated nodes are genuinely disjoint. -/
private theorem window_disjoint (x : ι → ℝ) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|) :
    Pairwise (Disjoint on nodeWindow x g) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro u hu hv
  change x i - g / 4 ≤ u ∧ u < x i + g / 4 at hu
  change x j - g / 4 ≤ u ∧ u < x j + g / 4 at hv
  have hs := hsep i j hij
  rcases le_total (x i) (x j) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hs
    linarith [hu.2, hv.1]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hs
    linarith [hv.2, hu.1]

/-- Every capturing rectangle lies in the full averaging strip. -/
private theorem rect_subset_strip (x : ι → ℝ) {g a : ℝ} (hg : 0 < g) (hga : g ≤ a)
    (i : ι) : nodeWindow x g i ×ˢ baseWindow x a i ⊆
      {p : ℝ × ℝ | a ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 2 * a} := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  change x i - g / 4 ≤ u ∧ u < x i + g / 4 at hu
  change x i - 7 * a / 4 ≤ v ∧ v ≤ x i - 5 * a / 4 at hv
  constructor <;> dsimp only <;> linarith [hu.1, hu.2, hv.1, hv.2]

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

private lemma measurable_widthStrip (a : ℝ) : MeasurableSet (widthStrip a) := by
  exact (measurableSet_Icc.preimage (measurable_fst.sub measurable_snd))

private lemma differenceEnergy_bound (x : ι → ℝ) (c : ι → ℂ) (p : ℝ × ℝ) :
    ‖differenceEnergy x c p‖ ≤ (2 * ∑ i, ‖c i‖) ^ 2 := by
  have hc : 0 ≤ ∑ i, ‖c i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (c i))
  have h := (norm_sub_le (prefix x c p.1) (prefix x c p.2)).trans
    (add_le_add (norm_prefix_le x c p.1) (norm_prefix_le x c p.2))
  rw [differenceEnergy, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [h]) 2

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
        (Measure.measurePreserving_neg (volume : Measure ℝ))).comp
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
    classical
    funext p
    change (if a ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 2 * a then
      Complex.normSq (prefix x c p.1 - prefix x c p.2) else 0) =
      (if a ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 2 * a then
        Complex.normSq (prefix x c p.1 - prefix x c (p.1 - (p.1 - p.2))) else 0)
    rw [show p.1 - (p.1 - p.2) = p.2 by ring]
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
    classical
    funext p
    change (if a ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 2 * a then
      Complex.normSq (prefix x c p.1 - prefix x c p.2) else 0) =
      (if a ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 2 * a then
        Complex.normSq (prefix x c p.1 - prefix x c (p.1 - (p.1 - p.2))) else 0)
    rw [show p.1 - (p.1 - p.2) = p.2 by ring]
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
