/- GID: D5/S3/Analytic/Oscillation/SmoothedSpectrumCounting
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SmoothedSpectrumCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded count discrepancy gives a uniform variance cap for smoothed spectrum counts. -/

import D5.S3.Analytic.Oscillation.OrdinateCounting
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import OmegaBuild.Commands

compile_only_with_mathlib

/-! Bounded count discrepancy gives a uniform variance cap for smoothed spectrum counts. -/

namespace D5.S3.Analytic.Oscillation.SmoothedSpectrumCounting

noncomputable section

namespace CutDensity

open MeasureTheory Set Filter Finset
open scoped Topology


open D5.S3.Analytic.Oscillation.OrdinateCounting

def countMain (C x : ℝ) : ℝ := x * (Real.log (x / C) - 1) / C

def countDensity (C H : ℝ) : ℝ → ℝ :=
  (Ioc C H).indicator (fun x => Real.log (x / C) / C)

private lemma countDensity_continuousOn {C H : ℝ} (hC : 0 < C) :
    ContinuousOn (fun x : ℝ => Real.log (x / C) / C) (Icc C H) := by
  intro x hx
  have hlog : ContinuousAt Real.log (x / C) :=
    Real.continuousAt_log (div_pos (hC.trans_le hx.1) hC).ne'
  have hd : ContinuousAt (fun t : ℝ => t / C) x :=
    (continuous_id.div_const C).continuousAt
  exact ((hlog.comp (f := fun t : ℝ => t / C) hd).div_const C).continuousWithinAt

private lemma countDensity_integrable {C H : ℝ} (hC : 0 < C) :
    Integrable (countDensity C H) := by
  rw [countDensity, integrable_indicator_iff measurableSet_Ioc]
  exact (countDensity_continuousOn hC).integrableOn_Icc.mono_set Ioc_subset_Icc_self

private lemma countMain_deriv {C x : ℝ} (hC : 0 < C) (hx : 0 < x) :
    HasDerivAt (countMain C) (Real.log (x / C) / C) x := by
  have hlog := (Real.hasDerivAt_log (div_pos hx hC).ne').comp x
    ((hasDerivAt_id x).div_const C)
  convert ((hasDerivAt_id x).mul (hlog.sub_const 1)).div_const C using 1
  · rfl
  · change Real.log (x / C) / C =
      (1 * (Real.log (x / C) - 1) + x * ((x / C)⁻¹ * (1 / C))) / C
    field_simp [hC.ne', hx.ne']
    ring

private lemma prefix_countDensity {C H t : ℝ} (hC : 0 < C) (hH : C ≤ H) :
    (∫ x in Iic t, countDensity C H x) =
      if C ≤ t then countMain C (min t H) - countMain C C else 0 := by
  have hs : Ioc C H ∩ Iic t = Ioc C (min t H) := by
    ext x
    simp only [mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, le_min_iff]
    tauto
  rw [countDensity, integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc, hs]
  by_cases ht : C ≤ t
  · rw [ite_eq_left ht, ← intervalIntegral.integral_of_le (le_min ht hH)]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · rw [uIcc_of_le (le_min ht hH)]
      exact fun x hx => countMain_deriv hC (hC.trans_le hx.1)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (le_min ht hH)]
      exact countDensity_continuousOn hC
  · rw [ite_eq_right ht, Set.Ioc_eq_empty (not_lt_of_ge (min_le_left t H |>.trans (le_of_not_ge ht))), Measure.restrict_empty, integral_zero_measure]

def copies {J : Type*} (s : Finset J) (m : J → ℕ) : Finset (Σ j : J, Fin (m j)) :=
  s.sigma (fun _ => univ)

private lemma prefix_cut_eq (S : Spectrum) (H t : ℝ) :
    (((copies (S.cut H) S.mult).filter (fun j => S.gamma j.1 ≤ t)).card : ℝ) = S.N (min t H) := by
  classical
  have he : (copies (S.cut H) S.mult).filter (fun j => S.gamma j.1 ≤ t) =
      copies (S.cut (min t H)) S.mult := by
    ext j
    simp only [copies, mem_filter, mem_sigma, Spectrum.cut,
      Set.Finite.mem_toFinset, Set.mem_ofPred_eq, le_min_iff]
    tauto
  rw [he, copies, card_sigma, Spectrum.N]
  simp only [card_univ, Fintype.card_fin]

lemma uniform_cumulative_bound (S : Spectrum) {C D : ℝ} (hC : 0 < C)
    (hcount : ∀ t, C ≤ t → |(S.N t : ℝ) - countMain C t| ≤ D) :
    ∀ H, C ≤ H → ∀ t,
      |(((copies (S.cut H) S.mult).filter (fun j => S.gamma j.1 ≤ t)).card : ℝ) -
        ∫ x in Iic t, countDensity C H x| ≤ max (S.N C : ℝ) (D + |countMain C C|) := by
  intro H hH t
  rw [prefix_cut_eq, prefix_countDensity hC hH]
  by_cases ht : C ≤ t
  · rw [ite_eq_left ht, sub_sub_eq_add_sub, add_sub_right_comm]
    exact (abs_add_le _ _).trans ((add_le_add_left (hcount _ (le_min ht hH)) _).trans (le_max_right _ _))
  · rw [ite_eq_right ht, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
    exact (count_mono S ((min_le_left _ _).trans (le_of_not_ge ht))).trans (le_max_left _ _)

private lemma countDensity_range {C H : ℝ} (hC : 1 ≤ C) (hH : 1 < H) (x : ℝ) :
    0 ≤ countDensity C H x ∧ countDensity C H x ≤ Real.log H / C := by
  have hC0 := zero_lt_one.trans_le hC
  by_cases hx : x ∈ Ioc C H
  · rw [countDensity, indicator_of_mem hx]
    have hlo : 1 ≤ x / C := (le_div_iff₀ hC0).2 (by simpa using hx.1.le)
    have hhi : x / C ≤ H := (div_le_iff₀ hC0).2
      (hx.2.trans (le_mul_of_one_le_right (zero_lt_one.trans hH).le hC))
    exact ⟨div_nonneg (Real.log_nonneg hlo) hC0.le,
      div_le_div_of_nonneg_right (Real.log_le_log (zero_lt_one.trans_le hlo) hhi) hC0.le⟩
  · rw [countDensity, indicator_of_notMem hx]
    exact ⟨le_rfl, div_nonneg (Real.log_pos hH).le hC0.le⟩

lemma cumulative_lip {C H : ℝ} (hC : 1 ≤ C) (hH : 1 < H)
    (x y : ℝ) (hxy : x ≤ y) :
    (∫ t in Iic y, countDensity C H t) - (∫ t in Iic x, countDensity C H t) ≤
      (Real.log H / C) * (y - x) := by
  have hs : Iic y \ Iic x = Ioc x y := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_Ioc, not_le]
    exact and_comm
  rw [← setIntegral_sdiff measurableSet_Iic (countDensity_integrable (zero_lt_one.trans_le hC)).integrableOn
     (Iic_subset_Iic.2 hxy), hs]
  calc
    _ ≤ ∫ t in Ioc x y, Real.log H / C := by
      apply setIntegral_mono_on (countDensity_integrable (zero_lt_one.trans_le hC)).integrableOn
        (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc
      exact fun t _ => (countDensity_range hC hH t).2
    _ = _ := by simp [hxy, mul_comm]

private lemma countMain_mono {C : ℝ} (hC : 0 < C) :
    MonotoneOn (countMain C) (Ici C) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici C)
  · exact fun x hx => (countMain_deriv hC (hC.trans_le hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    exact (countMain_deriv hC (hC.trans hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(countMain_deriv hC (hC.trans hx)).deriv]
    exact div_nonneg (Real.log_nonneg ((le_div_iff₀ hC).2 (by simpa using hx.le))) hC.le

lemma eventual_count_bound (S : Spectrum) {C D : ℝ} (hC : 0 < C)
    (hbound : ∀ᶠ H : ℝ in atTop, |(S.N H : ℝ) - countMain C H| ≤ D) :
    ∃ E : ℝ, ∀ H : ℝ, C ≤ H → |(S.N H : ℝ) - countMain C H| ≤ E := by
  obtain ⟨A, hA⟩ := eventually_atTop.1 hbound
  let U := max C A
  refine ⟨max D ((S.N U : ℝ) + max |countMain C C| |countMain C U|), ?_⟩
  intro H hH
  by_cases hHU : U ≤ H
  · exact (hA H ((le_max_right C A).trans hHU)).trans (le_max_left _ _)
  · have hHU' := (le_of_not_ge hHU)
    have hF₁ := countMain_mono hC Set.self_mem_Ici hH hH
    have hF₂ := countMain_mono hC hH (show U ∈ Ici C from le_max_left C A) hHU'
    have hF : |countMain C H| ≤ max |countMain C C| |countMain C U| := by
      rw [abs_le]
      constructor
      · linarith [le_max_left |countMain C C| |countMain C U|, neg_abs_le (countMain C C)]
      · exact hF₂.trans ((le_abs_self _).trans (le_max_right _ _))
    exact (abs_sub _ _).trans ((add_le_add (by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact count_mono S hHU') hF).trans (le_max_right _ _))

end CutDensity

namespace MainDensityLimit

open Filter MeasureTheory Set
open scoped Topology


private def relativeDensity (C H x : ℝ) : ℝ :=
  if C ≤ H * x ∧ x ≤ 1 then Real.log (H * x / C) / Real.log H else 0

private lemma relativeDensity_bounds {C H : ℝ} (hC : 1 ≤ C) (hH : 1 < H) (x : ℝ) :
    0 ≤ relativeDensity C H x ∧ relativeDensity C H x ≤ 1 := by
  unfold relativeDensity
  split_ifs with hx
  · have hC0 : 0 < C := zero_lt_one.trans_le hC
    have hL := Real.log_pos hH
    have hHx : C ≤ H * x := hx.1
    have hxi : x ≤ 1 := hx.2
    have hx0 : 0 < x := by
      by_contra! hxp
      have hprod := mul_nonpos_of_nonneg_of_nonpos (zero_le_one.trans hH.le) hxp
      linarith
    have hlow : 1 ≤ H * x / C := (le_div_iff₀ hC0).2 (by simpa using hHx)
    have hhigh : H * x / C ≤ H := by
      apply (div_le_iff₀ hC0).2
      exact mul_le_mul_of_nonneg_left (hxi.trans hC) (zero_le_one.trans hH.le)
    exact ⟨div_nonneg (Real.log_nonneg hlow) hL.le,
      (div_le_one hL).2 (Real.log_le_log (zero_lt_one.trans_le hlow) hhigh)⟩
  · exact ⟨le_rfl, zero_le_one⟩

private lemma relativeDensity_tendsto (C : ℝ) (hC : 1 ≤ C) (xH : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (ht : Tendsto xH atTop (𝓝 x)) :
    Tendsto (fun H : ℝ => relativeDensity C H (xH H)) atTop (𝓝 1) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hxC0 : 0 < x / C := div_pos hx.1 hC0
  have ht' : Tendsto (fun H : ℝ => xH H / C) atTop (𝓝 (x / C)) := ht.div_const C
  have hl : Tendsto (fun H : ℝ => Real.log (xH H / C)) atTop (𝓝 (Real.log (x / C))) :=
    (Real.continuousAt_log hxC0.ne').tendsto.comp ht'
  have hratio := hl.div_atTop Real.tendsto_log_atTop
  have hlimit : Tendsto (fun H : ℝ => 1 + Real.log (xH H / C) / Real.log H) atTop (𝓝 1) := by
    simpa only [add_zero] using hratio.const_add 1
  apply hlimit.congr'
  have hHx : Tendsto (fun H : ℝ => H * xH H) atTop atTop := tendsto_id.atTop_mul_pos hx.1 ht
  filter_upwards [eventually_gt_atTop (1 : ℝ), ht.eventually (Ioo_mem_nhds hx.1 hx.2),
    hHx.eventually_ge_atTop C] with H hH hxx hHC
  unfold relativeDensity
  rw [ite_eq_left ⟨hHC, hxx.2.le⟩, mul_div_assoc, Real.log_mul
    (zero_lt_one.trans hH).ne' (div_pos hxx.1 hC0).ne', add_div, div_self (Real.log_pos hH).ne']

private lemma measurable_relativeDensity (C H : ℝ) : Measurable (relativeDensity C H) := by
  unfold relativeDensity
  refine Measurable.ite (measurableSet_le measurable_const (measurable_const.mul measurable_id) |>.inter
    (measurableSet_le measurable_id measurable_const)) ?_ measurable_const
  exact ((Real.measurable_log.comp ((measurable_const.mul measurable_id).div_const C)).div_const _)

private theorem normalized_density_limit (C : ℝ) (hC : 1 ≤ C) (δ : ℝ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (g : ℝ → ℝ) (hg : Integrable g) (hgM : Measurable g) :
    Tendsto (fun H : ℝ => ∫ v in Ioo (0 : ℝ) 1,
      ((∫ u : ℝ, relativeDensity C H (v - δ H * u) * g u) - ∫ u : ℝ, g u) ^ 2)
      atTop (𝓝 0) := by
  let A (H v : ℝ) := ∫ u : ℝ, relativeDensity C H (v - δ H * u) * g u
  let m := ∫ u : ℝ, g u
  let K := ∫ u : ℝ, ‖g u‖
  have hAmeas (H : ℝ) : StronglyMeasurable (A H) := by
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    exact ((measurable_relativeDensity C H).comp
      (measurable_fst.sub (measurable_const.mul measurable_snd))).mul (hgM.comp measurable_snd)
  have hdom (H v : ℝ) (hH : 1 < H) (u : ℝ) :
      ‖relativeDensity C H (v - δ H * u) * g u‖ ≤ ‖g u‖ := by
    have hb := relativeDensity_bounds hC hH (v - δ H * u)
    rw [norm_mul, Real.norm_of_nonneg hb.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  have hpoint (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) 1) : Tendsto (fun H => A H v) atTop (𝓝 m) := by
    have ht (u : ℝ) : Tendsto (fun H => v - δ H * u) atTop (𝓝 v) := by
      simpa only [zero_mul, sub_zero] using (hδ.mul_const u).const_sub v
    have h := tendsto_integral_filter_of_dominated_convergence
      (F := fun H u => relativeDensity C H (v - δ H * u) * g u) (f := g)
      (fun u => ‖g u‖)
      (Eventually.of_forall fun H => (((measurable_relativeDensity C H).comp
        (measurable_const.sub (measurable_const.mul measurable_id))).mul hgM).aestronglyMeasurable)
      ((eventually_gt_atTop (1 : ℝ)).mono fun H hH => ae_of_all _ (hdom H v hH)) hg.norm
      (ae_of_all _ fun u => by
        simpa only [one_mul] using (relativeDensity_tendsto C hC _ hv (ht u)).mul_const (g u))
    exact h
  have hK : 0 ≤ K := integral_nonneg fun _ => norm_nonneg _
  have hpointB (H v : ℝ) (hH : 1 < H) : ‖A H v - m‖ ≤ 2 * K := by
    have hAi : Integrable (fun u => relativeDensity C H (v - δ H * u) * g u) := by
      exact hg.norm.mono' (((measurable_relativeDensity C H).comp
        (measurable_const.sub (measurable_const.mul measurable_id))).mul hgM).aestronglyMeasurable
        (ae_of_all _ (hdom H v hH))
    have hA : ‖A H v‖ ≤ K := (norm_integral_le_integral_norm _).trans
      (integral_mono hAi.norm hg.norm (hdom H v hH))
    calc
      _ ≤ ‖A H v‖ + ‖m‖ := norm_sub_le _ _
      _ ≤ K + K := add_le_add hA (norm_integral_le_integral_norm _)
      _ = _ := by ring
  simpa only [integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (F := fun H v => (A H v - m) ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => (2 * K) ^ 2)
      (Eventually.of_forall fun H => (((hAmeas H).sub stronglyMeasurable_const).pow 2).aestronglyMeasurable)
      ((eventually_gt_atTop (1 : ℝ)).mono fun H hH => ae_of_all _ fun v => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hpointB H v hH) _)
      (integrable_const _)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using ((hpoint v hv).sub_const m).pow 2))

end MainDensityLimit

namespace PrefixDiscrepancy

open Filter MeasureTheory Set Finset
open scoped Topology


def prefixCount {J : Type*} (s : Finset J) (g : J → ℝ) (t : ℝ) : ℝ :=
  (s.filter (fun j => g j ≤ t)).card

private lemma prefix_count_mul_eq_sum {J : Type*} (s : Finset J) (g : J → ℝ)
    (q : ℝ → ℝ) (t : ℝ) :
    prefixCount s g t * q t = ∑ j ∈ s, (Ici (g j)).indicator q t := by
  classical
  simp only [prefixCount, indicator, Set.mem_Ici, ← sum_filter, sum_const, nsmul_eq_mul]

private lemma prefix_discrepancy_integral {J : Type*} (s : Finset J) (g : J → ℝ) (q G F : ℝ → ℝ)
    (hq : Integrable q) (hF : Measurable F)
    (hG : ∀ u, (∫ t in Ioi u, q t) = G u)
    (D : ℝ) (hD : ∀ t, |prefixCount s g t - F t| ≤ D) :
    |(∑ j ∈ s, G (g j)) - ∫ t : ℝ, F t * q t| ≤ D * ∫ t : ℝ, |q t| := by
  have hterm (j : J) : Integrable ((Ici (g j)).indicator q) :=
    hq.indicator measurableSet_Ici
  have hprefix (h : ℝ → ℝ) : (fun t => prefixCount s g t * h t) =
      fun t => ∑ j ∈ s, (Ici (g j)).indicator h t := by
    funext t
    exact prefix_count_mul_eq_sum s g h t
  have hcount : Measurable (prefixCount s g) := by
    have h := hprefix (fun _ => 1)
    simp only [mul_one] at h
    change Measurable (fun t => prefixCount s g t)
    rw [h]
    exact Finset.measurable_sum _ fun j _ => measurable_const.indicator measurableSet_Ici
  have hdiff : Integrable (fun t => (prefixCount s g t - F t) * q t) :=
    hq.bdd_mul (c := D) (hcount.sub hF).aestronglyMeasurable
      (ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using hD t)
  have hCountInt : Integrable (fun t => prefixCount s g t * q t) := by
    rw [hprefix]
    exact integrable_finsetSum _ fun j _ => hterm j
  have hFInt : Integrable (fun t => F t * q t) := by
    convert hCountInt.sub hdiff using 1
    ext t
    simp only [Pi.sub_apply]
    ring
  have hsum : (∫ t : ℝ, prefixCount s g t * q t) = ∑ j ∈ s, G (g j) := by
    rw [hprefix, integral_finsetSum _ (fun j _ => hterm j)]
    apply sum_congr rfl
    intro j _
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, hG]
  rw [← hsum, ← integral_sub hCountInt hFInt]
  simp only [← sub_mul, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ t : ℝ, ‖(prefixCount s g t - F t) * q t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, D * ‖q t‖ := by
      apply integral_mono hdiff.norm (hq.norm.const_mul D)
      intro t
      change ‖(prefixCount s g t - F t) * q t‖ ≤ D * ‖q t‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hD t) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

private lemma scaled_derivative_tail (g g' : ℝ → ℝ) (hderiv : ∀ u, HasDerivAt g (g' u) u)
    (hlim : Tendsto g atBot (𝓝 0)) (hg' : Integrable g') (a x γ : ℝ) (ha : 0 < a) :
    (∫ t in Ioi γ, a * g' (a * (x - t))) = g (a * (x - γ)) := by
  have hin : Integrable (fun t : ℝ => a * g' (a * (x - t))) := by
    have hs := hg'.comp_mul_left' ha.ne'
    exact (hs.comp_sub_left x).const_mul a
  have hfun (t : ℝ) : HasDerivAt (fun u : ℝ => -g (a * (x - u)))
      (a * g' (a * (x - t))) t := by
    have hinner : HasDerivAt (fun u : ℝ => a * (x - u)) (-a) t := by
      simpa only [id_eq, mul_neg, mul_one] using ((hasDerivAt_id t).const_sub x).const_mul a
    have h := ((hderiv _).comp t hinner).neg
    change HasDerivAt (fun u : ℝ => -g (a * (x - u))) (-(g' (a * (x - t)) * -a)) t at h
    simpa only [mul_neg, neg_neg, mul_comm a] using h
  have ht : Tendsto (fun t : ℝ => -g (a * (x - t))) atTop (𝓝 0) := by
    have hx : Tendsto (fun t : ℝ => x - t) atTop atBot := by
      refine tendsto_atBot.mpr fun b => ?_
      filter_upwards [eventually_ge_atTop (x - b)] with t ht
      linarith
    have hax : Tendsto (fun t : ℝ => a * (x - t)) atTop atBot := (tendsto_const_mul_atBot_of_pos ha).2 hx
    simpa using (hlim.comp hax).neg
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (a := γ) (fun t _ => hfun t)
    hin.integrableOn ht

private lemma prefix_density_integral (p q G : ℝ → ℝ) (hp : Integrable p) (hq : Integrable q)
    (hG : ∀ u, (∫ t in Ioi u, q t) = G u) :
    (∫ u : ℝ, p u * G u) = ∫ t : ℝ, (∫ u in Iic t, p u) * q t := by
  let S : Set (ℝ × ℝ) := {z | z.1 ≤ z.2}
  let f : ℝ × ℝ → ℝ := S.indicator (fun z => p z.1 * q z.2)
  have hS : MeasurableSet S := measurableSet_le measurable_fst measurable_snd
  have hf : Integrable f (volume.prod volume) := (hp.mul_prod hq).indicator hS
  have hleft (u t : ℝ) : f (u, t) = p u * (Ici u).indicator q t := by
    by_cases h : u ≤ t <;> simp [f, S, Set.indicator, h]
  have hright (u t : ℝ) : f (u, t) = (Iic t).indicator p u * q t := by
    by_cases h : u ≤ t <;> simp [f, S, Set.indicator, h]
  calc
    _ = ∫ u : ℝ, ∫ t : ℝ, f (u, t) := by
      simp_rw [hleft, integral_const_mul, integral_indicator measurableSet_Ici,
        integral_Ici_eq_integral_Ioi, hG]
    _ = ∫ t : ℝ, ∫ u : ℝ, f (u, t) := by exact integral_integral_swap hf
    _ = _ := by simp_rw [hright, integral_mul_const, integral_indicator measurableSet_Iic]

private theorem count_smooth_error_le {J : Type*} (s : Finset J) (γ : J → ℝ) (p g g' : ℝ → ℝ)
    (hp : Integrable p) (hp0 : ∀ u, 0 ≤ p u)
    (hderiv : ∀ u, HasDerivAt g (g' u) u)
    (hlim : Tendsto g atBot (𝓝 0)) (hg' : Integrable g')
    (D : ℝ) (hD : ∀ t, |prefixCount s γ t - ∫ u in Iic t, p u| ≤ D)
    (a x : ℝ) (ha : 0 < a) :
    |(∑ j ∈ s, g (a * (x - γ j))) - ∫ u : ℝ, p u * g (a * (x - u))|
      ≤ D * ∫ u : ℝ, |g' u| := by
  let F (t : ℝ) := ∫ u in Iic t, p u
  let G (u : ℝ) := g (a * (x - u))
  let q (t : ℝ) := a * g' (a * (x - t))
  have hFm : Monotone F := by
    intro u v huv
    exact setIntegral_mono_set hp.integrableOn (ae_of_all _ hp0) (Set.Iic_subset_Iic.mpr huv).eventuallySubset
  have hq : Integrable q := ((hg'.comp_mul_left' ha.ne').comp_sub_left x).const_mul a
  have hG : ∀ u, (∫ t in Ioi u, q t) = G u := fun u =>
    scaled_derivative_tail g g' hderiv hlim hg' a x u ha
  have hQ : (∫ t : ℝ, |q t|) = ∫ u : ℝ, |g' u| := by
    simp only [q, abs_mul, abs_of_pos ha]
    rw [integral_const_mul]
    change a * (∫ t : ℝ, (fun z => |g' (a * z)|) (x - t)) = _
    rw [integral_sub_left_eq_self (fun z : ℝ => |g' (a * z)|) volume x,
      Measure.integral_comp_mul_left (fun z : ℝ => |g' z|),
      smul_eq_mul, abs_of_pos (inv_pos.mpr ha), ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  have h := prefix_discrepancy_integral s γ q G F hq hFm.measurable hG D hD
  rw [← prefix_density_integral p q G hp hq hG, hQ] at h
  exact h

end PrefixDiscrepancy

namespace VarianceUpper

open Filter MeasureTheory
open scoped Topology


private theorem variance_upper {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (A B : ℝ → X → ℝ) (D V : ℝ)
    (hA : ∀ᶠ H : ℝ in atTop, Integrable (fun x => (A H x) ^ 2) μ)
    (hB : ∀ᶠ H : ℝ in atTop, Integrable (fun x => (B H x) ^ 2) μ)
    (hclose : ∀ᶠ H : ℝ in atTop, ∀ᵐ x ∂μ, |A H x - B H x| ≤ D)
    (hAlim : Tendsto (fun H : ℝ => ∫ x, (A H x) ^ 2 ∂μ) atTop (𝓝 V))
    (hBlim : Tendsto (fun H : ℝ => ∫ x, (B H x) ^ 2 ∂μ) atTop (𝓝 0)) : V ≤ D^2 := by
  have hε (ε : ℝ) (hε0 : 0 < ε) : V ≤ (1 + ε) * D^2 := by
    have hmajor : ∀ᶠ H : ℝ in atTop, (∫ x, (A H x) ^ 2 ∂μ) ≤
        (1 + ε) * D^2 + (1 + ε⁻¹) * (∫ x, (B H x) ^ 2 ∂μ) := by
      filter_upwards [hA, hB, hclose] with H hAi hBi hHi
      have hpoint : ∀ᵐ x ∂μ, (A H x)^2 ≤ (1 + ε) * D^2 + (1 + ε⁻¹) * (B H x)^2 := by
        filter_upwards [hHi] with x hx
        have hD0 := (abs_nonneg _).trans hx
        have hs : (A H x - B H x)^2 ≤ D^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hD0] using hx)
        have hYoung : 0 ≤ ε * (A H x - B H x)^2 - 2 * (A H x - B H x) * B H x + ε⁻¹ * (B H x)^2 := by
          have hz := sq_nonneg (ε * (A H x - B H x) - B H x)
          apply (mul_nonneg_iff_of_pos_left hε0).mp
          rw [mul_add, ← mul_assoc ε ε⁻¹, mul_inv_cancel₀ hε0.ne', one_mul]
          nlinarith only [hz]
        calc
          _ ≤ (1 + ε) * (A H x - B H x)^2 + (1 + ε⁻¹) * (B H x)^2 := by nlinarith only [hYoung]
          _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hs (show 0 ≤ 1 + ε by positivity)) _
      calc
        _ ≤ ∫ x, (1 + ε) * D^2 + (1 + ε⁻¹) * (B H x)^2 ∂μ :=
          integral_mono_ae hAi ((integrable_const _).add (hBi.const_mul _)) hpoint
        _ = _ := by
          rw [integral_add (integrable_const _) (hBi.const_mul (1 + ε⁻¹)), integral_const]
          rw [integral_const_mul]
          rw [probReal_univ, one_smul]

    have hb : Tendsto (fun H : ℝ => (1 + ε) * D^2 + (1 + ε⁻¹) * (∫ x, (B H x) ^ 2 ∂μ)) atTop
        (𝓝 ((1 + ε) * D^2)) := by
      simpa only [mul_zero, add_zero] using (hBlim.const_mul (1 + ε⁻¹)).const_add _
    exact le_of_tendsto_of_tendsto hAlim hb hmajor
  have hlim : Tendsto (fun ε : ℝ => (1 + ε) * D^2) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (D^2)) := by
    have ht : Continuous (fun ε : ℝ => (1 + ε) * D^2) := by fun_prop
    have h0 := ht.continuousWithinAt (s := Set.Ioi (0 : ℝ)) (x := 0)
    rw [ContinuousWithinAt] at h0
    simpa only [add_zero, one_mul] using h0
  exact ge_of_tendsto hlim (by filter_upwards [self_mem_nhdsWithin] with ε hε0; exact hε ε hε0)

end VarianceUpper

open Filter MeasureTheory Set Finset
open D5.S3.Analytic.Oscillation.OrdinateCounting
open scoped Topology FourierTransform SchwartzMap

def meanScale (H : ℝ) : ℝ := Real.log H / (2 * Real.pi)

def smoothCount (S : Spectrum) (g : ℝ → ℝ) (H x : ℝ) : ℝ :=
  ∑ j ∈ CutDensity.copies (S.cut H) S.mult, g (meanScale H * (x - S.gamma j.1))

lemma meanScale_tendsto : Tendsto meanScale atTop atTop :=
  Real.tendsto_log_atTop.atTop_div_const (by positivity)

lemma meanScale_pos {H : ℝ} (hH : 1 < H) : 0 < meanScale H :=
  div_pos (Real.log_pos hH) (by positivity)

set_option backward.isDefEq.respectTransparency false in
private lemma uniform_smooth_error (S : Spectrum) (g : 𝓢(ℝ, ℝ)) {E H : ℝ}
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E)
    (hH : 1 < H) (hHC : 2 * Real.pi ≤ H) (x : ℝ) :
    |smoothCount S g H x -
      ∫ u : ℝ, CutDensity.countDensity (2 * Real.pi) H u * g (meanScale H * (x - u))|
      ≤ max (S.N (2 * Real.pi) : ℝ) (E + |CutDensity.countMain (2 * Real.pi) (2 * Real.pi)|) *
        ∫ u : ℝ, ‖deriv g u‖ := by
  have hC : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hC0 := zero_lt_one.trans_le hC
  have hderiv : Integrable (deriv g) := by
    exact (SchwartzMap.derivCLM ℝ ℝ g).integrable
  let sites := CutDensity.copies (S.cut H) S.mult
  let ordinate (j : Σ i : S.index, Fin (S.mult i)) := S.gamma j.1
  let density := CutDensity.countDensity (2 * Real.pi) H
  let D := max (S.N (2 * Real.pi) : ℝ) (E + |CutDensity.countMain (2 * Real.pi) (2 * Real.pi)|)
  have hbound : ∀ t, |PrefixDiscrepancy.prefixCount sites ordinate t -
      ∫ u in Iic t, density u| ≤ D :=
    CutDensity.uniform_cumulative_bound S hC0 hcount H hHC
  have hsmooth := PrefixDiscrepancy.count_smooth_error_le sites ordinate density (g : ℝ → ℝ)
    (deriv g) (CutDensity.countDensity_integrable hC0)
    (fun u => (CutDensity.countDensity_range hC hH u).1) g.hasDerivAt
    (g.tendsto_cocompact.mono_left atBot_le_cocompact) hderiv D hbound
    (meanScale H) x (meanScale_pos hH)
  change |(∑ j ∈ sites, g (meanScale H * (x - ordinate j))) -
    ∫ u : ℝ, density u * g (meanScale H * (x - u))| ≤ D * ∫ u : ℝ, ‖deriv g u‖
  simpa only [Real.norm_eq_abs] using hsmooth

private lemma density_as_relative {C H : ℝ} (hC : 1 ≤ C) (hH : 1 < H) (v : ℝ) :
    CutDensity.countDensity C H (H * v) =
      (Real.log H / C) * MainDensityLimit.relativeDensity C H v := by
  have hC0 := zero_lt_one.trans_le hC
  have hH0 := zero_lt_one.trans hH
  have hv : H * v ≤ H ↔ v ≤ 1 := by
    have h := (mul_le_mul_iff_right₀ (a := H) (b := v) (c := 1) hH0)
    simpa only [mul_one] using h
  have hL := (Real.log_pos hH).ne'
  by_cases hCv : C ≤ H * v ∧ v ≤ 1
  · rcases hCv with ⟨hCv, hv1⟩
    rcases hCv.eq_or_lt with heq | hlt
    · rw [CutDensity.countDensity, indicator_of_notMem (fun hm => hm.1.ne heq),
        MainDensityLimit.relativeDensity, ite_eq_left ⟨hCv, hv1⟩, ← heq, div_self hC0.ne',
        Real.log_one, zero_div, mul_zero]
    · have hs : H * v ∈ Ioc C H := ⟨hlt, hv.2 hv1⟩
      rw [CutDensity.countDensity, indicator_of_mem hs, MainDensityLimit.relativeDensity,
        ite_eq_left ⟨hlt.le, hv1⟩]
      field_simp
  · have hs : H * v ∉ Ioc C H := fun hm => hCv ⟨hm.1.le, hv.1 hm.2⟩
    rw [CutDensity.countDensity, indicator_of_notMem hs, MainDensityLimit.relativeDensity,
      ite_eq_right hCv, mul_zero]

private lemma normalized_reference {H : ℝ} (hH : 1 < H) (g : ℝ → ℝ) (v : ℝ) :
    (∫ u : ℝ, CutDensity.countDensity (2 * Real.pi) H u *
      g (meanScale H * (H * v - u))) =
      ∫ t : ℝ, MainDensityLimit.relativeDensity (2 * Real.pi) H (v - (meanScale H * H)⁻¹ * t) * g t := by
  let a := meanScale H
  let q (u : ℝ) := CutDensity.countDensity (2 * Real.pi) H (H * v - u) * g (a * u)
  have ha := meanScale_pos hH
  have hH0 := zero_lt_one.trans hH
  have hC : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have he (u : ℝ) : H * v - a⁻¹ * u = H * (v - (a * H)⁻¹ * u) := by
    field_simp [ha.ne', hH0.ne']
  calc
    _ = ∫ u : ℝ, q (H * v - u) := by simp only [q, sub_sub_cancel, a]
    _ = ∫ u : ℝ, q u := integral_sub_left_eq_self q volume (H * v)
    _ = a⁻¹ * ∫ t : ℝ, q (a⁻¹ * t) := by
      rw [Measure.integral_comp_inv_mul_left, abs_of_pos ha, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ ha.ne', one_mul]
    _ = _ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      dsimp only [q]
      rw [he, density_as_relative hC hH, ← mul_assoc a (a⁻¹), mul_inv_cancel₀ ha.ne', one_mul]
      change a⁻¹ * (a * _ * _) = _
      have hcan : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
      simp only [← mul_assoc, hcan, one_mul]
      rfl

private lemma normalized_reference_limit (g : 𝓢(ℝ, ℝ)) :
    Tendsto (fun H : ℝ => ∫ v in Ioo (0 : ℝ) 1,
      ((∫ u : ℝ, CutDensity.countDensity (2 * Real.pi) H u *
        g (meanScale H * (H * v - u))) - ∫ u : ℝ, g u) ^ 2) atTop (𝓝 0) := by
  have hC : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have ht := MainDensityLimit.normalized_density_limit (2 * Real.pi) hC _
    ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp (meanScale_tendsto.atTop_mul_atTop₀ tendsto_id))
    g g.integrable g.continuous.measurable
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
  simp_rw [normalized_reference hH, Function.comp_apply, id_eq]

lemma normalized_variance_upper (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E V : ℝ)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E)
    (hlim : Tendsto (fun H : ℝ => ∫ v in Ioo (0 : ℝ) 1,
      (smoothCount S g H (H * v) - ∫ u : ℝ, g u) ^ 2) atTop (𝓝 V)) :
    V ≤ (max (S.N (2 * Real.pi) : ℝ) (E + |CutDensity.countMain (2 * Real.pi) (2 * Real.pi)|) *
      ∫ u : ℝ, ‖deriv g u‖) ^ 2 := by
  let μ := (volume : Measure ℝ).restrict (Ioo 0 1)
  let b := ∫ u : ℝ, g u
  let A (H v : ℝ) := smoothCount S g H (H * v) - b
  let B (H v : ℝ) := (∫ u : ℝ, CutDensity.countDensity (2 * Real.pi) H u *
      g (meanScale H * (H * v - u))) - b
  let D := max (S.N (2 * Real.pi) : ℝ) (E + |CutDensity.countMain (2 * Real.pi) (2 * Real.pi)|) *
      ∫ u : ℝ, ‖deriv g u‖
  have : IsProbabilityMeasure μ := by
    rw [isProbabilityMeasure_iff]
    simp [μ, Measure.restrict_apply, Real.volume_Ioo]
  have hAi (H : ℝ) : Integrable (fun v => (A H v) ^ 2) μ := by
    have hc : Continuous (fun v => (A H v) ^ 2) := by
      unfold A smoothCount
      fun_prop
    apply hc.integrableOn_Icc.mono_set
    exact Ioo_subset_Icc_self
  have hBi : ∀ᶠ H : ℝ in atTop, Integrable (fun v => (B H v) ^ 2) μ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
    let δ := (meanScale H * H)⁻¹
    let Q (v : ℝ) := ∫ u : ℝ,
      MainDensityLimit.relativeDensity (2 * Real.pi) H (v - δ * u) * g u
    have hQ : StronglyMeasurable Q := by
      apply StronglyMeasurable.integral_prod_right
      apply Measurable.stronglyMeasurable
      exact ((MainDensityLimit.measurable_relativeDensity (2 * Real.pi) H).comp
        (measurable_fst.sub (measurable_const.mul measurable_snd))).mul
        (g.continuous.measurable.comp measurable_snd)
    have hBQ : B H = fun v => Q v - b := by
      funext v
      exact congrArg (· - b) (normalized_reference hH g v)
    rw [hBQ]
    let K := ∫ u : ℝ, ‖g u‖
    have hC : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hpoint (v u : ℝ) : ‖MainDensityLimit.relativeDensity (2 * Real.pi) H
        (v - δ * u) * g u‖ ≤ ‖g u‖ := by
      have hb := MainDensityLimit.relativeDensity_bounds hC hH (v - δ * u)
      rw [norm_mul, Real.norm_of_nonneg hb.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hb.2
    have hbound (v : ℝ) : ‖Q v - b‖ ≤ K + K := by
      have hi : Integrable (fun u => MainDensityLimit.relativeDensity (2 * Real.pi) H
          (v - δ * u) * g u) := by
        refine g.integrable.norm.mono' ?_ (ae_of_all _ (hpoint v))
        exact (((MainDensityLimit.measurable_relativeDensity (2 * Real.pi) H).comp
          (measurable_const.sub (measurable_const.mul measurable_id))).mul
          g.continuous.measurable).aestronglyMeasurable
      have hq : ‖Q v‖ ≤ K := (norm_integral_le_integral_norm _).trans
        (integral_mono hi.norm g.integrable.norm (hpoint v))
      exact (norm_sub_le _ _).trans (add_le_add hq (norm_integral_le_integral_norm _))
    exact (integrable_const ((K + K) ^ 2) (μ := μ)).mono'
      (((hQ.sub stronglyMeasurable_const).pow 2).aestronglyMeasurable)
      (ae_of_all _ fun v => by
        simp only [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound v) 2)
  have hclose : ∀ᶠ H : ℝ in atTop, ∀ᵐ v ∂μ, |A H v - B H v| ≤ D := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (2 * Real.pi)] with H hH hHC
    exact ae_of_all _ fun v => by
      simpa only [A, B, sub_sub_sub_cancel_right] using uniform_smooth_error S g hcount hH hHC (H * v)
  exact VarianceUpper.variance_upper μ A B D V (Eventually.of_forall hAi) hBi hclose hlim
    (normalized_reference_limit g)

lemma normalized_count_tends_one (S : Spectrum) (E : ℝ)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    Tendsto (fun H : ℝ => (S.N H : ℝ) / (H * meanScale H)) atTop (𝓝 1) := by
  let C := 2 * Real.pi
  let d (H : ℝ) := H * meanScale H
  have hC : 0 < C := by dsimp [C]; positivity
  have hd : Tendsto d atTop atTop := tendsto_id.atTop_mul_atTop₀ meanScale_tendsto
  have herror : Tendsto (fun H : ℝ => ((S.N H : ℝ) - CutDensity.countMain C H) / d H)
      atTop (𝓝 0) := by
    have hE : Tendsto (fun H => E / d H) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hd
    refine squeeze_zero_norm' ?_ hE
    filter_upwards [eventually_ge_atTop C, hd.eventually_gt_atTop (0 : ℝ)] with H hH hdH
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hdH]
    exact div_le_div_of_nonneg_right (hcount H hH) hdH.le
  have hmain : Tendsto (fun H : ℝ => CutDensity.countMain C H / d H) atTop (𝓝 1) := by
    have hl : Tendsto (fun H : ℝ => (Real.log C + 1) / Real.log H) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    apply (show Tendsto (fun H => 1 - (Real.log C + 1) / Real.log H) atTop (𝓝 1) by
      simpa only [sub_zero] using hl.const_sub 1).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
    have hH0 := zero_lt_one.trans hH
    rw [CutDensity.countMain, Real.log_div hH0.ne' hC.ne']
    dsimp only [d, meanScale]
    change _ = _ / (H * (Real.log H / C))
    field_simp [(Real.log_pos hH).ne', hH0.ne', hC.ne']
    ring
  have hsum := hmain.add herror
  rw [add_zero] at hsum
  exact hsum.congr (fun H => by dsimp [d]; rw [← add_div]; congr 1; ring)

lemma copies_card (S : Spectrum) (H : ℝ) :
    ((CutDensity.copies (S.cut H) S.mult).card : ℝ) = S.N H := by
  rw [CutDensity.copies, card_sigma, Spectrum.N]
  simp only [card_univ, Fintype.card_fin]

end
end D5.S3.Analytic.Oscillation.SmoothedSpectrumCounting
