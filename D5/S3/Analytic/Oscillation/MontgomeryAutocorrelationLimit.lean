/- GID: D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Montgomery unit band determines the unweighted autocorrelation limit under bounded discrepancy. -/

import D5.S3.Analytic.Oscillation.MontgomeryWindow
import D5.S3.Analytic.Oscillation.SmoothedSpectrumCounting
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The Montgomery unit band determines the unweighted autocorrelation limit under bounded discrepancy. -/

namespace D5.S3.Analytic.Oscillation.MontgomeryAutocorrelationLimit

noncomputable section

open SmoothedSpectrumCounting

namespace KernelLimit

open Filter MeasureTheory
open scoped Topology

open D5.S3.Analytic.Oscillation.MontgomeryWindow

private lemma peak_error_integral_bound
    (f E : ℝ → ℝ) (hf : Integrable f) (hE : Measurable E)
    (L B M e : ℝ) (hL : 0 < L) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hbound : ∀ u, ‖f u‖ ≤ M)
    (hcompact : ∀ u, 1 < |u| → f u = 0)
    (herr : ∀ u, |u| ≤ 1 → ‖E u‖ ≤ B * exponentialWeight (L * u) + e) :
    Integrable (fun u => E u * f u) ∧
    ‖∫ u : ℝ, E u * f u‖ ≤ (B * M) / L + e * ∫ u : ℝ, ‖f u‖ := by
  let K (u : ℝ) := exponentialWeight (L * u)
  let Q (u : ℝ) := (B * M) * K u + e * ‖f u‖
  have hK0 (u : ℝ) : 0 ≤ K u := (Real.exp_pos _).le
  have hK : Integrable K := exponentialWeight_integrable.comp_mul_left' hL.ne'
  have hQ : Integrable Q := (hK.const_mul (B * M)).add (hf.norm.const_mul e)
  have hdom (u : ℝ) : ‖E u * f u‖ ≤ Q u := by
    by_cases hu : |u| ≤ 1
    · rw [norm_mul]
      calc
        _ ≤ (B * K u + e) * ‖f u‖ := mul_le_mul_of_nonneg_right (herr u hu) (norm_nonneg _)
        _ = (B * K u) * ‖f u‖ + e * ‖f u‖ := add_mul _ _ _
        _ ≤ Q u := by
          dsimp [Q]
          rw [mul_right_comm B M]
          exact add_le_add_left (mul_le_mul_of_nonneg_left (hbound u) (mul_nonneg hB (hK0 u))) _
    · rw [hcompact u (lt_of_not_ge hu), mul_zero, norm_zero]
      dsimp [Q]
      simp only [hcompact u (lt_of_not_ge hu), abs_zero, mul_zero, add_zero]
      exact mul_nonneg (mul_nonneg hB hM) (hK0 u)
  have hi := hQ.mono' (hE.aestronglyMeasurable.mul hf.aestronglyMeasurable) (ae_of_all _ hdom)
  refine ⟨hi, (norm_integral_le_integral_norm _).trans ((integral_mono hi.norm hQ hdom).trans_eq ?_)⟩
  have hm : (∫ u : ℝ, exponentialWeight u) = 1 := by simpa using exponentialWeight_cosine 0 0
  have hs : (∫ u : ℝ, K u) = L⁻¹ := by
    rw [show K = fun u => exponentialWeight (L * u) from rfl,
      Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hL), hm, smul_eq_mul, mul_one]
  change (∫ u : ℝ, (B * M) * K u + e * ‖f u‖) = _
  have he := integral_add (hK.const_mul (B * M)) (hf.norm.const_mul e)
  rw [he, integral_const_mul, hs, integral_const_mul, div_eq_mul_inv]

private lemma kernelDilationLimit (K f : ℝ → ℝ) (hK : Integrable K) (hK_mass : (∫ x, K x) = 1)
    (hf : Continuous f) (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    Tendsto (fun L : ℝ => ∫ x : ℝ, L * K (L * x) * f x) atTop (𝓝 (f 0)) := by
  have hlim : Tendsto (fun L : ℝ => ∫ x : ℝ, K x * f (L⁻¹ * x)) atTop
      (𝓝 (∫ x : ℝ, K x * f 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => B * ‖K x‖)
    · exact Eventually.of_forall fun L => hK.aestronglyMeasurable.mul
        (hf.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · exact Eventually.of_forall fun L => ae_of_all _ fun x => by
        rw [norm_mul, mul_comm B]
        exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    · exact hK.norm.const_mul B
    · exact ae_of_all _ fun x => tendsto_const_nhds.mul
        ((hf.continuousAt (x := 0)).tendsto.comp (by
          simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const x))
  rw [integral_mul_const, hK_mass, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hscale := Measure.integral_comp_mul_left (fun t : ℝ => K t * f (L⁻¹ * t)) L
  simp only [abs_of_pos (inv_pos.mpr hL), smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul] at hscale
  calc
    (∫ x : ℝ, K x * f (L⁻¹ * x)) = L * (∫ x : ℝ, K (L * x) * f x) := by rw [hscale, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
    _ = ∫ x : ℝ, L * K (L * x) * f x := by simp only [mul_assoc, integral_const_mul]

private lemma profile_integral_limit (f : ℝ → ℝ)
    (hf : Continuous f) (hfint : Integrable f) (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ x, ‖f x‖ ≤ M)
    (scale : ℝ → ℝ) (hscale : Tendsto scale atTop atTop)
    (P : ℝ → ℝ → ℝ) (hP : ∀ L, Measurable (P L))
    (c ε : ℝ → ℝ) (hc : Tendsto c atTop (𝓝 1)) (hε : Tendsto ε atTop (𝓝 0))
    (hcompact : ∀ x, 1 < |x| → f x = 0)
    (herror : ∀ᶠ L : ℝ in atTop, ∀ x, |x| ≤ 1 →
      |P L x - (c L * (scale L * exponentialWeight (scale L * x)) + |x|)| ≤ B * exponentialWeight (scale L * x) + ε L) :
    Tendsto (fun L : ℝ => ∫ x : ℝ, P L x * f x) atTop
      (𝓝 (f 0 + ∫ x : ℝ, |x| * f x)) := by
  let K := exponentialWeight
  have hK : Integrable K := exponentialWeight_integrable
  have hK_mass : (∫ x, K x) = 1 := by simpa [K] using exponentialWeight_cosine 0 0
  have hpeak := (kernelDilationLimit K f hK hK_mass hf M hfB).comp hscale
  let E (L x : ℝ) := P L x - (c L * (scale L * exponentialWeight (scale L * x)) + |x|)
  have hlin : Integrable (fun x : ℝ => |x| * f x) := by
    refine (hfint.norm).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
    by_cases hx : |x| ≤ 1
    · rw [norm_mul, Real.norm_of_nonneg (abs_nonneg x)]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
    · simp [hcompact x (lt_of_not_ge hx)]
  have hmain : Tendsto (fun L : ℝ =>
      c L * (∫ x : ℝ, scale L * K (scale L * x) * f x) + ∫ x : ℝ, |x| * f x) atTop
      (𝓝 (f 0 + ∫ x : ℝ, |x| * f x)) := by
    simpa only [one_mul, Function.comp_apply] using (hc.mul hpeak).add_const _
  have hbound : ∀ᶠ L : ℝ in atTop, 0 < scale L ∧ Integrable (fun x => E L x * f x) ∧
      ‖∫ x, E L x * f x‖ ≤ (B * M) / scale L + ε L * ∫ x, ‖f x‖ := by
    filter_upwards [hscale.eventually_gt_atTop (0 : ℝ), herror] with L hL herr
    have hE : Measurable (E L) := by
      unfold E exponentialWeight
      exact (hP L).sub (by fun_prop)
    have h := peak_error_integral_bound f (E L) hfint hE (scale L) B M (ε L)
      hL hB hM hfB hcompact (fun x hx => by simpa only [E, Real.norm_eq_abs] using herr x hx)
    exact ⟨hL, h⟩
  have hE0 : Tendsto (fun L : ℝ => ∫ x, E L x * f x) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun L => (B * M) / scale L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hscale
    refine squeeze_zero_norm' (hbound.mono (fun _ h => h.2.2)) ?_
    simpa only [zero_mul, add_zero] using hsmall.add (hε.mul_const (∫ x, ‖f x‖))
  have hsum := hmain.add hE0
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hbound] with L hL
  have hpeak_int : Integrable (fun x => scale L * K (scale L * x) * f x) :=
    ((hK.comp_mul_left' hL.1.ne').const_mul (scale L)).mul_bdd hf.aestronglyMeasurable (ae_of_all _ hfB)
  calc
    _ = ∫ x : ℝ, (c L * (scale L * K (scale L * x) * f x) + |x| * f x) + E L x * f x := by
      have hadd := integral_add ((hpeak_int.const_mul (c L)).add hlin) hL.2.1
      simp only [Pi.add_apply] at hadd
      rw [hadd, integral_add (hpeak_int.const_mul (c L)) hlin, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp [E]; ring

end KernelLimit

namespace ShellCount

open Finset


private theorem count_shell_le {J : Type*} (s : Finset J) (g : J → ℝ)
    (F : ℝ → ℝ) (a D : ℝ) (ha : 0 < a)
    (hF : ∀ x y, x ≤ y → F y - F x ≤ a * (y - x))
    (hD : ∀ x, |((s.filter (fun j => g j ≤ x)).card : ℝ) - F x| ≤ D)
    (center : ℝ) (k : ℕ) :
    ((s.filter (fun j => ⌊|a * (center - g j)|⌋₊ = k)).card : ℝ) ≤ 4 + 4 * D := by
  classical
  let count (x : ℝ) := s.filter (fun j => g j ≤ x)
  have hinterval (x y : ℝ) (hxy : x ≤ y) :
      (((count y \ count x).card : ℝ)) ≤ a * (y - x) + 2 * D := by
    have hsub : count x ⊆ count y := by
      intro j hj
      exact mem_filter.2 ⟨(mem_filter.1 hj).1, (mem_filter.1 hj).2.trans hxy⟩
    have hcard := card_sdiff_add_card_eq_card hsub
    have heq : ((count y \ count x).card : ℝ) + (count x).card = (count y).card := by
      exact_mod_cast hcard
    have hx := (abs_le.mp (hD x)).1
    have hy := (abs_le.mp (hD y)).2
    linarith [hF x y hxy]
  let loL := center - ((k : ℝ) + 2) / a
  let hiL := center - (k : ℝ) / a
  let loR := center + ((k : ℝ) - 1) / a
  let hiR := center + ((k : ℝ) + 1) / a
  have hlenL : a * (hiL - loL) = 2 := by
    dsimp [loL, hiL]
    field_simp
    <;> ring
  have hlenR : a * (hiR - loR) = 2 := by
    dsimp [loR, hiR]
    field_simp
    <;> ring
  have hleL : loL ≤ hiL := by nlinarith
  have hleR : loR ≤ hiR := by nlinarith
  have hsub : s.filter (fun j => ⌊|a * (center - g j)|⌋₊ = k) ⊆
      (count hiL \ count loL) ∪ (count hiR \ count loR) := by
    intro j hj
    obtain ⟨hj, hshell⟩ := mem_filter.1 hj
    obtain ⟨hl, hu⟩ := (Nat.floor_eq_iff (abs_nonneg _)).mp hshell
    by_cases hjleft : g j ≤ center
    · have hv : 0 ≤ a * (center - g j) := mul_nonneg ha.le (sub_nonneg.mpr hjleft)
      rw [abs_of_nonneg hv] at hl hu
      apply Finset.mem_union_left
      apply mem_sdiff.2
      constructor
      · apply mem_filter.2
        refine ⟨hj, ?_⟩
        dsimp [hiL]
        have h : (k : ℝ) / a ≤ center - g j := (div_le_iff₀ ha).2 (by simpa only [mul_comm a] using hl)
        linarith
      · intro hh
        have hjl := (mem_filter.1 hh).2
        dsimp [loL] at hjl
        have hu' : center - g j < ((k : ℝ) + 1) / a := (lt_div_iff₀ ha).2 (by simpa only [mul_comm a] using hu)
        have hx : (0 : ℝ) < 1 / a := by positivity
        rw [show ((k : ℝ) + 2) / a = ((k : ℝ) + 1) / a + 1 / a by ring] at hjl
        linarith
    · have hv : a * (center - g j) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le
        (sub_nonpos.mpr (le_of_not_ge hjleft))
      rw [abs_of_nonpos hv, ← mul_neg, neg_sub] at hl hu
      apply Finset.mem_union_right
      apply mem_sdiff.2
      constructor
      · apply mem_filter.2
        refine ⟨hj, ?_⟩
        dsimp [hiR]
        have h : g j - center < ((k : ℝ) + 1) / a := (lt_div_iff₀ ha).2 (by simpa only [mul_comm a] using hu)
        linarith
      · intro hh
        have hjr := (mem_filter.1 hh).2
        dsimp [loR] at hjr
        have hl' : (k : ℝ) / a ≤ g j - center := (div_le_iff₀ ha).2 (by simpa only [mul_comm a] using hl)
        have hx : (0 : ℝ) < 1 / a := by positivity
        rw [sub_div] at hjr
        linarith
  calc
    _ ≤ (((count hiL \ count loL) ∪ (count hiR \ count loR)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((count hiL \ count loL).card : ℝ) + (count hiR \ count loR).card := by
      exact_mod_cast card_union_le (count hiL \ count loL) (count hiR \ count loR)
    _ ≤ _ := by
      have hl := hinterval loL hiL hleL
      have hr := hinterval loR hiR hleR
      rw [hlenL] at hl
      rw [hlenR] at hr
      linarith

end ShellCount

namespace Weights

open Finset


private theorem remove_lorentz_weight {J : Type*} (s : Finset J) (g : J → ℝ) (f : ℝ → ℝ)
    (a : ℝ) (ha : 0 < a) (D : ℕ) (B : ℕ → ℝ) (hB : Summable B)
    (hB0 : ∀ k, 0 ≤ B k)
    (hlocal : ∀ i ∈ s, ∀ k : ℕ,
      (s.filter fun j => ⌊|a * (g i - g j)|⌋₊ = k).card ≤ D)
    (hprofile : ∀ u, u ^ 2 * |f u| ≤ B ⌊|u|⌋₊) :
    |(∑ i ∈ s, ∑ j ∈ s, f (a * (g i - g j))) -
      ∑ i ∈ s, ∑ j ∈ s, (4 / (4 + (g i - g j) ^ 2)) * f (a * (g i - g j))| ≤
      (s.card : ℝ) * D * (∑' k, B k) / (4 * a ^ 2) := by
  classical
  let shells (i j : J) : ℕ := ⌊|a * (g i - g j)|⌋₊
  let error (i j : J) : ℝ :=
    f (a * (g i - g j)) - (4 / (4 + (g i - g j) ^ 2)) * f (a * (g i - g j))
  have hscale : 0 < 4 * a ^ 2 := by positivity
  have hpoint (i j : J) : |error i j| ≤ B (shells i j) / (4 * a ^ 2) := by
    let d := g i - g j
    change |f (a * d) - (4 / (4 + d^2)) * f (a * d)| ≤ _
    have hden : 0 < 4 + d ^ 2 := by positivity
    have he : f (a * d) - (4 / (4 + d^2)) * f (a * d) =
        (d^2 / (4 + d^2)) * f (a * d) := by field_simp; ring
    rw [he, abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) hden.le)]
    refine (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (sq_nonneg d)
      (by norm_num : 0 < (4 : ℝ)) (by linarith [sq_nonneg d])) (abs_nonneg _)).trans ?_
    apply (le_div_iff₀ hscale).2
    have hb := hprofile (a * d)
    change (a * d)^2 * |f (a * d)| ≤ B (shells i j) at hb
    convert hb using 1 <;> ring
  have hrow (i : J) (hi : i ∈ s) :
      (∑ j ∈ s, B (shells i j)) ≤ (D : ℝ) * (∑' k, B k) := by
    rw [← sum_fiberwise_of_maps_to (fun j hj => mem_image_of_mem (shells i) hj)
      (fun j => B (shells i j))]
    calc
      _ ≤ ∑ k ∈ s.image (shells i), (D : ℝ) * B k := by
        apply sum_le_sum
        intro k _
        change (∑ j ∈ s.filter (fun j => shells i j = k), B (shells i j)) ≤ _
        calc
          _ = ((s.filter (fun j => shells i j = k)).card : ℝ) * B k := by
            rw [← nsmul_eq_mul, ← sum_const]
            apply sum_congr rfl
            intro j hj
            rw [(mem_filter.mp hj).2]
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hlocal i hi k) (hB0 k)
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (hB.sum_le_tsum _ (fun k _ => hB0 k)) (by positivity)
  simp_rw [← sum_sub_distrib]
  change |∑ i ∈ s, ∑ j ∈ s, error i j| ≤ _
  calc
    _ ≤ ∑ i ∈ s, |∑ j ∈ s, error i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, B (shells i j) / (4 * a ^ 2) := by
      apply sum_le_sum
      intro i _
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => hpoint i j)
    _ = (∑ i ∈ s, ∑ j ∈ s, B (shells i j)) / (4 * a ^ 2) := by simp_rw [div_eq_mul_inv, sum_mul]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hscale.le
      calc
        _ ≤ ∑ i ∈ s, (D : ℝ) * (∑' k, B k) := sum_le_sum hrow
        _ = _ := by rw [sum_const, nsmul_eq_mul, mul_assoc]

end Weights

namespace FourierTest

open MeasureTheory Finset
open scoped FourierTransform


private def posPhase (d u : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * u * d) * Complex.I)

private lemma posPhase_norm (d u : ℝ) : ‖posPhase d u‖ = 1 := by
  simp [posPhase, Complex.norm_exp, Complex.mul_re]

private lemma integrate_inverse_mode (f : ℝ → ℂ) (hf : Integrable f)
    (hff : Integrable (𝓕 f)) (hc : Continuous f) (d : ℝ) :
    (∫ u : ℝ, posPhase d u * 𝓕 f u) = f d := by
  rw [← hf.fourierInv_fourier_eq hff hc.continuousAt, Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [posPhase, smul_eq_mul]
  congr 3
  ring

private lemma weighted_pair_integral {J : Type*} (s : Finset J) (g : J → ℝ) (f : ℝ → ℂ)
    (hf : Integrable f) (hff : Integrable (𝓕 f)) (hc : Continuous f) (a : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s,
      ((4 / (4 + (g i - g j)^2) : ℝ) : ℂ) * f (a * (g i - g j))) =
      ∫ u : ℝ, (∑ i ∈ s, ∑ j ∈ s,
        ((4 / (4 + (g i - g j)^2) : ℝ) : ℂ) * posPhase (a * (g i - g j)) u) * 𝓕 f u := by
  let d (i j : J) := a * (g i - g j)
  let c (i j : J) : ℂ := ((4 / (4 + (g i - g j)^2) : ℝ) : ℂ)
  have hterm (i j : J) : Integrable (fun u => (c i j * posPhase (d i j) u) * 𝓕 f u) := by
    refine hff.bdd_mul (c := ‖c i j‖) ?_ ?_
    · exact (show Continuous (fun u => c i j * posPhase (d i j) u) by
        unfold posPhase
        fun_prop).aestronglyMeasurable
    · exact ae_of_all _ (fun u => by rw [norm_mul, posPhase_norm, mul_one])
  change (∑ i ∈ s, ∑ j ∈ s, c i j * f (d i j)) =
      ∫ u : ℝ, (∑ i ∈ s, ∑ j ∈ s, c i j * posPhase (d i j) u) * 𝓕 f u
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum s (fun j _ => hterm i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun u => c i j * posPhase (d i j) u * 𝓕 f u) =
      (fun u => c i j * (posPhase (d i j) u * 𝓕 f u)) by funext u; rw [mul_assoc],
    integral_const_mul, integrate_inverse_mode f hf hff hc]

private theorem weighted_real_pair_integral {J : Type*} (s : Finset J) (g : J → ℝ) (f p : ℝ → ℝ)
    (hf : Integrable f) (hp : Integrable p) (hc : Continuous f)
    (hFourier : ∀ u, 𝓕 (fun t => (f t : ℂ)) u = (p u : ℂ)) (a : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s,
      (4 / (4 + (g i - g j)^2) : ℝ) * f (a * (g i - g j))) =
      ∫ u : ℝ, (∑ i ∈ s, ∑ j ∈ s,
        (4 / (4 + (g i - g j)^2) : ℝ) * Real.cos (2 * Real.pi * u * (a * (g i - g j)))) * p u := by
  have hFourier' := funext hFourier
  have hcf : Integrable (fun t => (f t : ℂ)) := hf.ofReal
  have hcp : Integrable (fun t => (p t : ℂ)) := hp.ofReal
  have heq := weighted_pair_integral s g (fun t => (f t : ℂ)) hcf
    (hFourier' ▸ hcp) (Complex.continuous_ofReal.comp hc) a
  rw [hFourier'] at heq
  have hterm (i j : J) : Integrable (fun u => ((4 / (4 + (g i - g j)^2) : ℝ) : ℂ) *
      posPhase (a * (g i - g j)) u * (p u : ℂ)) := by
    apply hcp.bdd_mul (c := ‖((4 / (4 + (g i - g j)^2) : ℝ) : ℂ)‖)
    · exact (show Continuous (fun u => ((4 / (4 + (g i - g j)^2) : ℝ) : ℂ) *
          posPhase (a * (g i - g j)) u) by unfold posPhase; fun_prop).aestronglyMeasurable
    · exact ae_of_all _ (fun u => by rw [norm_mul, posPhase_norm, mul_one])
  have hInt : Integrable (fun u => (∑ i ∈ s, ∑ j ∈ s,
      ((4 / (4 + (g i - g j)^2) : ℝ) : ℂ) * posPhase (a * (g i - g j)) u) * (p u : ℂ)) := by
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j
  have hreal := congrArg Complex.re heq
  have hrint := (integral_re hInt).symm
  change Complex.re (∫ u : ℝ, _) = (∫ u : ℝ, Complex.re _) at hrint
  rw [hrint] at hreal
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    Complex.re_sum, posPhase, Complex.exp_ofReal_mul_I_re] at hreal
  exact hreal

end FourierTest

namespace Multiplicity

open SmoothedSpectrumCounting.CutDensity (copies)

open Finset

private theorem sum_copies {J : Type*} (s : Finset J) (m : J → ℕ) (q : J → ℝ) :
    (∑ p ∈ copies s m, q p.1) = ∑ j ∈ s, (m j : ℝ) * q j := by
  rw [copies, sum_sigma]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

end Multiplicity

namespace Autocorrelation

open MeasureTheory
open scoped Convolution FourierTransform ComplexConjugate


private def complexify (g : ℝ → ℝ) (u : ℝ) : ℂ := g u

private lemma fourier_reflection (g : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (fun u => complexify g (-u)) ξ = conj (𝓕 (complexify g) ξ) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, ← integral_conj]
  calc
    _ = ∫ u : ℝ, Complex.exp (↑(-2 * Real.pi * (-u) * ξ) * Complex.I) * complexify g u := by
      simpa only [neg_neg] using
        (integral_neg_eq_self (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) *
          complexify g (-v)) volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      simp only [map_mul, complexify, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
      congr 2
      push_cast
      ring

def autocorrelation (g : ℝ → ℝ) (d : ℝ) : ℝ :=
  ∫ u : ℝ, g u * g (u + d)

private theorem fourier_autocorrelation (g : ℝ → ℝ) (hg : Integrable g) (hgC : Continuous g) (B : ℝ)
    (hB : ∀ u, ‖g u‖ ≤ B) :
    Integrable (autocorrelation g) ∧ Continuous (autocorrelation g) ∧
    ∀ ξ, 𝓕 (complexify (autocorrelation g)) ξ = (‖𝓕 (complexify g) ξ‖ ^ 2 : ℝ) := by
  let g₁ : ℝ → ℂ := fun u => complexify g (-u)
  let g₂ := complexify g
  let L := ContinuousLinearMap.mul ℂ ℂ
  have hg₂ : Integrable g₂ := hg.ofReal
  have hg₁ : Integrable g₁ := hg₂.comp_neg
  have hConv : complexify (autocorrelation g) = g₁ ⋆[L] g₂ := by
    funext d
    rw [convolution_def, ← integral_neg_eq_self _ volume]
    change (↑(∫ u : ℝ, g u * g (u + d)) : ℂ) =
      ∫ u : ℝ, (g (- -u) : ℂ) * (g (d - -u) : ℂ)
    simp only [neg_neg, sub_neg_eq_add, add_comm d, ← Complex.ofReal_mul, integral_complex_ofReal]
  have hcont : Continuous (g₁ ⋆[L] g₂) := by
    refine BddAbove.continuous_convolution_right_of_integrable L ⟨B, ?_⟩ hg₁
      (Complex.continuous_ofReal.comp hgC)
    rintro _ ⟨u, rfl⟩
    simpa only [g₂, complexify, Complex.norm_real] using hB u
  have hi : Integrable (g₁ ⋆[L] g₂) := hg₁.integrable_convolution L hg₂
  refine ⟨?_, ?_, ?_⟩
  · rw [← hConv] at hi
    exact Complex.reCLM.integrable_comp hi
  · rw [← hConv] at hcont
    exact Complex.continuous_re.comp hcont
  · intro ξ
    rw [hConv, Real.fourier_mul_convolution_eq hg₁ hg₂, fourier_reflection, mul_comm,
      Complex.mul_conj', Complex.ofReal_pow]

end Autocorrelation

open Filter MeasureTheory Set Finset
open D5.S3.Analytic.Oscillation.OrdinateCounting
open scoped Topology FourierTransform SchwartzMap

lemma copies_pair_sum (S : Spectrum) (H : ℝ) (q : S.index → S.index → ℝ) :
    (∑ p ∈ CutDensity.copies (S.cut H) S.mult, ∑ r ∈ CutDensity.copies (S.cut H) S.mult,
      q p.1 r.1) =
        ∑ j ∈ S.cut H, ∑ k ∈ S.cut H, (S.mult j : ℝ) * (S.mult k : ℝ) * q j k := by
  change (∑ p ∈ CutDensity.copies (S.cut H) S.mult, ∑ r ∈ CutDensity.copies (S.cut H) S.mult,
    q p.1 r.1) = _
  rw [Multiplicity.sum_copies (S.cut H) S.mult
    (fun j => ∑ r ∈ CutDensity.copies (S.cut H) S.mult, q j r.1)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Multiplicity.sum_copies (S.cut H) S.mult (q j), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

open D5.S3.Analytic.Oscillation.MontgomeryWindow (montgomery exponentialWeight
  exponentialWeight_integrable exponentialWeight_cosine)

private def complexSchwartz (g : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM g

def spectralTest (g : 𝓢(ℝ, ℝ)) (u : ℝ) : ℝ := ‖(𝓕 (complexSchwartz g) : 𝓢(ℝ, ℂ)) u‖ ^ 2

lemma spectralTest_eq (g : 𝓢(ℝ, ℝ)) (u : ℝ) :
    spectralTest g u = ‖𝓕 ((fun x => (g x : ℂ))) u‖ ^ 2 := by
  unfold spectralTest
  rw [SchwartzMap.fourier_coe]
  rfl

private lemma spectralTest_continuous (g : 𝓢(ℝ, ℝ)) : Continuous (spectralTest g) :=
  (SchwartzMap.continuous _).norm.pow 2

private lemma spectralTest_bounded (g : 𝓢(ℝ, ℝ)) :
    ∃ B : ℝ, ∀ u, ‖spectralTest g u‖ ≤ B := by
  let G := (𝓕 (complexSchwartz g) : 𝓢(ℝ, ℂ))
  refine ⟨(SchwartzMap.seminorm ℝ 0 0 G) ^ 2, fun u => ?_⟩
  change ‖‖G u‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℝ G u) 2

private lemma spectralTest_integrable (g : 𝓢(ℝ, ℝ)) : Integrable (spectralTest g) := by
  let G := (𝓕 (complexSchwartz g) : 𝓢(ℝ, ℂ))
  change Integrable (fun u => ‖G u‖ ^ 2)
  refine (G.integrable.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 G)).mono'
    (G.continuous.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ G u) (norm_nonneg _)

private lemma spectralTest_zero (g : 𝓢(ℝ, ℝ)) : spectralTest g 0 = (∫ x, g x) ^ 2 := by
  rw [spectralTest_eq, Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  change ‖(∫ x : ℝ, (g x : ℂ))‖ ^ 2 = _
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def UnitBandProfile (S : Spectrum) : Prop :=
  ∃ c e : ℝ → ℝ, Tendsto c atTop (𝓝 1) ∧ Tendsto e atTop (𝓝 0) ∧
  ∀ᶠ H : ℝ in atTop, ∀ u : ℝ, |u| ≤ 1 →
    |montgomery S u H - (c H * (Real.log H * Real.exp (-2 * Real.log H * |u|)) + |u|)| ≤ e H

/-- The pointwise error may include a bounded multiple of the unscaled exponential peak. -/
def ConcentratedUnitBandProfile (S : Spectrum) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
    ∀ᶠ H : ℝ in atTop, ∀ u : ℝ, |u| ≤ 1 →
      |montgomery S u H - (Real.log H * Real.exp (-2 * Real.log H * |u|) + |u|)| ≤
        B * Real.exp (-2 * Real.log H * |u|) + e H

/-- Pair-profile convergence against the squared Fourier transform of each fixed test. -/
def UnitBandTestLimit (S : Spectrum) : Prop :=
  ∀ g : 𝓢(ℝ, ℝ), (∀ u, 1 < |u| → 𝓕 (fun x => (g x : ℂ)) u = 0) →
    Tendsto (fun H : ℝ => ∫ u : ℝ, montgomery S u H * spectralTest g u) atTop
      (𝓝 ((∫ x : ℝ, g x) ^ 2 + ∫ u : ℝ, |u| * spectralTest g u))

private lemma band_integral_limit (S : Spectrum) (B : ℝ) (hB : 0 ≤ B)
    (c e : ℝ → ℝ) (hc : Tendsto c atTop (𝓝 1)) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ H : ℝ in atTop, ∀ u : ℝ, |u| ≤ 1 →
      |montgomery S u H - (c H * (Real.log H * Real.exp (-2 * Real.log H * |u|)) + |u|)| ≤
        B * Real.exp (-2 * Real.log H * |u|) + e H) :
    UnitBandTestLimit S := by
  intro g hg
  obtain ⟨M, hM⟩ := spectralTest_bounded g
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hP (H : ℝ) : Measurable (fun u => montgomery S u H) := by
    apply Continuous.measurable
    unfold montgomery
    fun_prop
  rw [← spectralTest_zero g]
  apply KernelLimit.profile_integral_limit (spectralTest g)
    (spectralTest_continuous g) (spectralTest_integrable g) B M hB hM0 hM
    Real.log Real.tendsto_log_atTop (fun H u => montgomery S u H) hP c e hc he
  · intro u hu
    rw [spectralTest_eq, hg u hu, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  · filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with H hh hH
    intro u hu
    simpa only [exponentialWeight, abs_mul, abs_of_pos (Real.log_pos hH), mul_assoc] using hh u hu

lemma unitBandTestLimit_of_uniform (S : Spectrum) (hS : UnitBandProfile S) :
    UnitBandTestLimit S := by
  obtain ⟨c, e, hc, he, hbound⟩ := hS
  refine band_integral_limit S 0 le_rfl c e hc he ?_
  simpa only [zero_mul, zero_add] using hbound

lemma unitBandTestLimit_of_concentrated (S : Spectrum) (hS : ConcentratedUnitBandProfile S) :
    UnitBandTestLimit S := by
  obtain ⟨B, hB, e, he, hbound⟩ := hS
  refine band_integral_limit S B hB (fun _ => 1) e tendsto_const_nhds he ?_
  simpa only [one_mul] using hbound

private def weightedAuto (S : Spectrum) (g : ℝ → ℝ) (H : ℝ) : ℝ :=
  ∑ p ∈ CutDensity.copies (S.cut H) S.mult, ∑ q ∈ CutDensity.copies (S.cut H) S.mult,
    (4 / (4 + (S.gamma p.1 - S.gamma q.1) ^ 2)) *
      Autocorrelation.autocorrelation g (meanScale H * (S.gamma p.1 - S.gamma q.1))

private lemma band_weighted_eq (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (H : ℝ) :
    weightedAuto S g H / (H * meanScale H) =
      ∫ u : ℝ, montgomery S u H * spectralTest g u := by
  let Q u := spectralTest g u
  let s := CutDensity.copies (S.cut H) S.mult
  let ordinate (j : Σ i : S.index, Fin (S.mult i)) := S.gamma j.1
  let f := Autocorrelation.autocorrelation g
  let a := meanScale H
  obtain ⟨hf, hfc, hF⟩ := Autocorrelation.fourier_autocorrelation g g.integrable g.continuous _
    (SchwartzMap.norm_le_seminorm ℝ g)
  have htest (u : ℝ) : 𝓕 (fun t => (f t : ℂ)) u = (Q u : ℂ) := by
    rw [show Q u = _ from spectralTest_eq g u]
    exact hF u
  have he := FourierTest.weighted_real_pair_integral s ordinate f Q hf
    (spectralTest_integrable g) hfc htest a
  change (∑ i ∈ s, ∑ j ∈ s,
    (4 / (4 + (ordinate i - ordinate j) ^ 2)) * f (a * (ordinate i - ordinate j))) /
    (H * a) = _
  rw [he, div_eq_mul_inv, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with u
  have hfreq (x : ℝ) : 2 * Real.pi * u * (a * x) = u * Real.log H * x := by
    dsimp only [a, meanScale]
    field_simp [Real.pi_ne_zero]
  simp_rw [hfreq]
  change ((∑ i ∈ s, ∑ j ∈ s, (4 / (4 + (ordinate i - ordinate j) ^ 2)) *
    Real.cos (u * Real.log H * (ordinate i - ordinate j))) * Q u) *
    (H * a)⁻¹ = _
  rw [show (∑ i ∈ s, ∑ j ∈ s, (4 / (4 + (ordinate i - ordinate j) ^ 2)) *
      Real.cos (u * Real.log H * (ordinate i - ordinate j))) = _ from
    copies_pair_sum S H (fun j k => (4 / (4 + (S.gamma j - S.gamma k) ^ 2)) *
      Real.cos (u * Real.log H * (S.gamma j - S.gamma k)))]
  have hnorm : (H * a)⁻¹ = 2 * Real.pi / (H * Real.log H) := by
    dsimp [a, meanScale]
    rw [show H * (Real.log H / (2 * Real.pi)) = (H * Real.log H) / (2 * Real.pi) by ring,
      inv_div]
  rw [hnorm, montgomery]
  rw [mul_assoc, mul_comm (Q u), ← mul_assoc, mul_comm _ (2 * Real.pi / (H * Real.log H))]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

open scoped Convolution

private lemma autocorrelation_schwartz (g : 𝓢(ℝ, ℝ)) :
    ∃ f : 𝓢(ℝ, ℝ), (f : ℝ → ℝ) = Autocorrelation.autocorrelation g := by
  let gc := complexSchwartz g
  let reflected := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv gc
  let L := ContinuousLinearMap.mul ℂ ℂ
  let f := SchwartzMap.convolution L reflected gc
  refine ⟨SchwartzMap.postcompCLM Complex.reCLM f, ?_⟩
  funext d
  change (f d).re = _
  rw [show f d = _ from SchwartzMap.convolution_apply L reflected gc d,
    convolution_def, ← integral_neg_eq_self _ volume]
  change (∫ u : ℝ, (g (- -u) : ℂ) * (g (d - -u) : ℂ)).re = _
  simp only [neg_neg, sub_neg_eq_add, add_comm d, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re, Autocorrelation.autocorrelation]

lemma schwartz_shell_majorant (f : 𝓢(ℝ, ℝ)) (m : ℕ) :
    ∃ B : ℕ → ℝ, Summable B ∧ (∀ k, 0 ≤ B k) ∧
      ∀ u : ℝ, |u| ^ m * |f u| ≤ B ⌊|u|⌋₊ := by
  let C := (SchwartzMap.seminorm ℝ m 0) f + 4 * (SchwartzMap.seminorm ℝ (m + 2) 0) f
  let B (k : ℕ) := C * (1 / ((k : ℝ) + 1) ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨B, ?_, (fun k => mul_nonneg hC (by positivity)), ?_⟩
  · apply Summable.mul_left
    have hs := (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2
      (Real.summable_one_div_nat_pow.2 (by decide : 1 < (2 : ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  · intro u
    let k := ⌊|u|⌋₊
    have hk : (k : ℝ) ≤ |u| := Nat.floor_le (abs_nonneg _)
    have hc₀ : 0 ≤ (SchwartzMap.seminorm ℝ m 0) f := apply_nonneg _ _
    have hc₂ : 0 ≤ (SchwartzMap.seminorm ℝ (m + 2) 0) f := apply_nonneg _ _
    by_cases h : k = 0
    · change _ ≤ B k
      rw [h]
      simp only [B, Nat.cast_zero, zero_add, one_pow, div_one, mul_one]
      have hf := SchwartzMap.norm_pow_mul_le_seminorm ℝ f m u
      simp only [Real.norm_eq_abs] at hf
      linarith
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      have hscale : ((k : ℝ) + 1)^2 ≤ 4 * |u|^2 := by
        have h := pow_le_pow_left₀ (by positivity : 0 ≤ (k : ℝ) + 1)
          (show (k : ℝ) + 1 ≤ 2 * |u| by linarith) 2
        nlinarith
      change _ ≤ B k
      unfold B
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity : 0 < ((k : ℝ) + 1)^2)).2
      have hf := SchwartzMap.norm_pow_mul_le_seminorm ℝ f (m + 2) u
      simp only [Real.norm_eq_abs, pow_add] at hf
      calc
        _ ≤ (|u| ^ m * |f u|) * (4 * |u| ^ 2) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = 4 * (|u| ^ m * |u| ^ 2 * |f u|) := by ring
        _ ≤ C := by
          have h₄ := mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 4)
          dsimp [C]
          linarith

lemma shells_bounded (S : Spectrum) (E : ℝ)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    ∃ D : ℕ, ∀ᶠ H : ℝ in atTop, ∀ z : ℝ, ∀ k : ℕ,
      ((CutDensity.copies (S.cut H) S.mult).filter
        (fun j => ⌊|meanScale H * (z - S.gamma j.1)|⌋₊ = k)).card ≤ D := by
  let C := 2 * Real.pi
  have hC : 1 ≤ C := by dsimp [C]; linarith [Real.pi_gt_three]
  let U := max (S.N C : ℝ) (E + |CutDensity.countMain C C|)
  obtain ⟨D, hD⟩ := exists_nat_gt (4 + 4 * U)
  refine ⟨D, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop C] with H hH hHC
  let F (t : ℝ) := ∫ u in Iic t, CutDensity.countDensity C H u
  intro z k
  have hb := ShellCount.count_shell_le (CutDensity.copies (S.cut H) S.mult)
    (fun j => S.gamma j.1) F (meanScale H) U (meanScale_pos hH)
    (CutDensity.cumulative_lip hC hH)
    (CutDensity.uniform_cumulative_bound S (zero_lt_one.trans_le hC) hcount H hHC) z k
  exact_mod_cast hb.trans hD.le

def unweightedAuto (S : Spectrum) (g : ℝ → ℝ) (H : ℝ) : ℝ :=
  ∑ p ∈ CutDensity.copies (S.cut H) S.mult, ∑ q ∈ CutDensity.copies (S.cut H) S.mult,
    Autocorrelation.autocorrelation g (meanScale H * (S.gamma p.1 - S.gamma q.1))

lemma spectral_unweighted_limit_of_test_limit (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hg : ∀ u, 1 < |u| → 𝓕 ((fun x => (g x : ℂ))) u = 0)
    (hS : UnitBandTestLimit S)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    Tendsto (fun H : ℝ => unweightedAuto S g H / (H * meanScale H)) atTop
      (𝓝 ((∫ x : ℝ, g x) ^ 2 + ∫ u : ℝ, |u| * spectralTest g u)) := by
  obtain ⟨f, hf⟩ := autocorrelation_schwartz g
  obtain ⟨B, hB, hB0, hdecay⟩ := schwartz_shell_majorant f 2
  obtain ⟨D, hD⟩ := shells_bounded S E hcount
  have hdecay' (u : ℝ) : u ^ 2 * |Autocorrelation.autocorrelation g u| ≤ B ⌊|u|⌋₊ := by
    simpa only [hf, sq_abs] using hdecay u
  have hdiff : Tendsto (fun H : ℝ => (unweightedAuto S g H - weightedAuto S g H) /
      (H * meanScale H)) atTop (𝓝 0) := by
    let c := (D : ℝ) * ∑' k, B k
    have hN := normalized_count_tends_one S E hcount
    have ha : Tendsto (fun H => 4 * meanScale H ^ 2) atTop atTop := by
      exact (meanScale_tendsto.atTop_mul_atTop₀ meanScale_tendsto).const_mul_atTop
        (show 0 < (4 : ℝ) by norm_num) |>.congr (fun H => by ring)
    refine squeeze_zero_norm' ?_ ((hN.mul_const c).div_atTop ha)
    filter_upwards [hD, eventually_gt_atTop (1 : ℝ)] with H hDH hH
    have haH := meanScale_pos hH
    have hden : 0 < H * meanScale H := mul_pos (zero_lt_one.trans hH) haH
    have h := Weights.remove_lorentz_weight (CutDensity.copies (S.cut H) S.mult)
      (fun j => S.gamma j.1) (Autocorrelation.autocorrelation g) (meanScale H) haH
      D B hB hB0 (fun i _ k => hDH (S.gamma i.1) k) hdecay'
    change |unweightedAuto S g H - weightedAuto S g H| ≤ _ at h
    rw [copies_card] at h
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
    refine (div_le_div_of_nonneg_right h hden.le).trans_eq ?_
    dsimp [c]
    ring
  have hw := (hS g hg).congr (fun H => (band_weighted_eq S g H).symm)
  simpa only [add_zero] using (hw.add hdiff).congr (fun H => by rw [← add_div]; congr 1; ring)

lemma spectral_unweighted_limit (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hg : ∀ u, 1 < |u| → 𝓕 ((fun x => (g x : ℂ))) u = 0)
    (hS : UnitBandProfile S)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    Tendsto (fun H : ℝ => unweightedAuto S g H / (H * meanScale H)) atTop
      (𝓝 ((∫ x : ℝ, g x) ^ 2 + ∫ u : ℝ, |u| * spectralTest g u)) :=
  spectral_unweighted_limit_of_test_limit S g E hg (unitBandTestLimit_of_uniform S hS) hcount

end
end D5.S3.Analytic.Oscillation.MontgomeryAutocorrelationLimit
