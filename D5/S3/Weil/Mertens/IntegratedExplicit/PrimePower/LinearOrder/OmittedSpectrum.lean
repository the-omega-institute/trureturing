/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/OmittedSpectrum
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/OmittedSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A linear bound for the omitted actual root densities under RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.SpectralSampling
import D5.S3.Weil.ZetaRvm.LocalCount
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHMobiusWindow
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

open Complex MeasureTheory Finset Set Function

open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (on_line)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

private def occurrenceFrequency (i : ℕ) : ℝ := (actualZero i).im

private theorem occurrence_dist_norm (hRH : RiemannHypothesis) {s : ℝ} (hs : 1 ≤ s) (i : ℕ) :
    ‖actualZero i‖ ≤ ‖(s : ℂ) - actualZero i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, on_line hRH i]
  nlinarith only [mul_nonneg (show 0 ≤ s by linarith) (show 0 ≤ s-1 by linarith)]

private theorem occurrence_half_le_norm (hRH : RiemannHypothesis) {s : ℝ} (hs : 1 ≤ s) (i : ℕ) :
    s/2 ≤ ‖(s : ℂ) - actualZero i‖ := by
  have h := Complex.abs_re_le_norm ((s : ℂ) - actualZero i)
  rw [Complex.sub_re, Complex.ofReal_re, on_line hRH i, abs_of_nonneg (by linarith)] at h
  linarith

private theorem occurrence_freq_abs_le (s : ℝ) (i : ℕ) :
    |occurrenceFrequency i| ≤ ‖(s : ℂ) - actualZero i‖ := by
  simpa [occurrenceFrequency] using Complex.abs_im_le_norm ((s : ℂ) - actualZero i)

private theorem occurrence_norm_pos (hRH : RiemannHypothesis) (i : ℕ) :
    0 < ‖actualZero i‖ := by
  have h := Complex.abs_re_le_norm (actualZero i)
  rw [on_line hRH i] at h
  norm_num at h
  linarith

private theorem occurrence_coeff_le (hRH : RiemannHypothesis) {s : ℝ} (hs : 1 ≤ s) (i : ℕ) :
    ‖rootCoeff s i‖ ≤ 2 * (‖actualZero i‖)⁻¹ := by
  have hnorm := occurrence_norm_pos hRH i
  have hhalf := occurrence_half_le_norm hRH hs i
  rw [rootCoeff, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ s), norm_mul]
  calc
    _ ≤ s / (‖actualZero i‖ * (s/2)) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity)
        (mul_le_mul_of_nonneg_left hhalf hnorm.le)
    _ = _ := by
      have : s ≠ 0 := by linarith
      field_simp

private theorem occurrence_coeff_phase_le {s : ℝ} (hs : 0 ≤ s) (i : ℕ) :
    ‖phaseDerivCoeff occurrenceFrequency (rootCoeff s) i‖ ≤ s * (‖actualZero i‖)⁻¹ := by
  have hf := occurrence_freq_abs_le s i
  unfold phaseDerivCoeff rootCoeff
  simp only [norm_mul, norm_div, norm_neg, Complex.norm_real, Complex.norm_I, one_mul,
    Real.norm_eq_abs, abs_of_nonneg hs]
  rw [div_mul_eq_mul_div]
  by_cases hz : ‖(s : ℂ) - actualZero i‖ = 0
  · simp [hz, mul_nonneg hs]
  · rw [show s * |occurrenceFrequency i| / (‖actualZero i‖ * ‖(s : ℂ) - actualZero i‖) =
        (s * (‖actualZero i‖)⁻¹) * (|occurrenceFrequency i| / ‖(s : ℂ) - actualZero i‖) by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one
      ((norm_nonneg _).lt_of_ne' hz)).mpr hf)

private def occurrenceIncrement (s : ℝ) (i : ℕ) : ℂ :=
  rootCoeff (s+1) i - rootCoeff s i

private theorem occurrenceIncrement_eq (hRH : RiemannHypothesis) {s : ℝ} (hs : 1 ≤ s) (i : ℕ) :
    occurrenceIncrement s i = 1 / (((s : ℂ) - actualZero i) * (((s+1 : ℝ) : ℂ) - actualZero i)) := by
  have hz := norm_pos_iff.mp (occurrence_norm_pos hRH i)
  have h₁ := norm_pos_iff.mp
    ((occurrence_norm_pos hRH i).trans_le (occurrence_dist_norm hRH hs i))
  have h₂ := norm_pos_iff.mp
    ((occurrence_norm_pos hRH i).trans_le (occurrence_dist_norm hRH (show 1 ≤ s+1 by linarith) i))
  unfold occurrenceIncrement rootCoeff
  push_cast at h₂ ⊢
  field_simp [hz, h₁, h₂]
  ring

private theorem occurrenceIncrement_le (hRH : RiemannHypothesis) {s q : ℝ}
    (hs : 1 ≤ s) (hq : 0 < q) (hsq : q/2 ≤ s) (i : ℕ) :
    ‖occurrenceIncrement s i‖ ≤ (4/q) * (‖actualZero i‖)⁻¹ := by
  have hnorm := occurrence_norm_pos hRH i
  have h₁ := occurrence_half_le_norm hRH hs i
  have h₂ := occurrence_dist_norm hRH (show 1 ≤ s+1 by linarith) i
  rw [occurrenceIncrement_eq hRH hs, norm_div, norm_one, norm_mul]
  calc
    _ ≤ 1 / ((q/4) * ‖actualZero i‖) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul (by linarith) h₂ hnorm.le (norm_nonneg _))
    _ = _ := by field_simp

private theorem occurrenceIncrement_phase_le (hRH : RiemannHypothesis) {s : ℝ} (hs : 1 ≤ s) (i : ℕ) :
    ‖phaseDerivCoeff occurrenceFrequency (occurrenceIncrement s) i‖ ≤ (‖actualZero i‖)⁻¹ := by
  have hnorm := occurrence_norm_pos hRH i
  have h₁ := occurrence_dist_norm hRH hs i
  have h₂ := occurrence_freq_abs_le (s+1) i
  rw [phaseDerivCoeff, occurrenceIncrement_eq hRH hs, norm_mul, norm_mul, norm_I, one_mul,
    norm_div, norm_one, norm_mul, norm_real, Real.norm_eq_abs]
  calc
    _ = (‖(s : ℂ) - actualZero i‖)⁻¹ *
        (|occurrenceFrequency i| / ‖((s+1 : ℝ) : ℂ) - actualZero i‖) := by
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ ≤ (‖(s : ℂ) - actualZero i‖)⁻¹ := mul_le_of_le_one_right (by positivity)
      ((div_le_one (hnorm.trans_le
        (occurrence_dist_norm hRH (show 1 ≤ s+1 by linarith) i))).mpr h₂)
    _ ≤ _ := inv_anti₀ hnorm h₁

private theorem occurrence_bin_majorant {T : Finset ℕ} {a : ℕ → ℂ} {b : ℤ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hb : ∀ k, ∑ i ∈ T with frequencyBin (occurrenceFrequency i) = k, (‖actualZero i‖)⁻¹ ≤ b k)
    (ha : ∀ i, ‖a i‖ ≤ C * (‖actualZero i‖)⁻¹) :
    ∀ k, binMass T occurrenceFrequency a k ≤ C * b k := by
  intro k
  unfold binMass
  calc
    _ ≤ ∑ i ∈ T with frequencyBin (occurrenceFrequency i) = k, C * (‖actualZero i‖)⁻¹ :=
      Finset.sum_le_sum fun i _ => ha i
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hb k) hC

private theorem occurrence_band_samples (hRH : RiemannHypothesis)
    {b : ℤ → ℝ} (hbs : Summable fun k => b k^2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T S : Finset ℕ) (v : ℕ → ℝ) (c : ℝ) (p q : ℕ),
      0 < p → p ≤ q → (q : ℝ) / 2 ≤ p →
      (∀ n ∈ S, n ∈ Finset.Icc p q) →
      (∀ i ∈ S, v i ∈ Set.Icc (c-1/2) (c+1/2)) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1/(q : ℝ) ≤ |v i-v j|) →
      (∀ k, ∑ i ∈ T with frequencyBin (occurrenceFrequency i) = k, (‖actualZero i‖)⁻¹ ≤ b k) →
      ∑ n ∈ S, ‖finiteModes T occurrenceFrequency (rootCoeff n) (v n)‖ ≤ K * q := by
  obtain ⟨K, hK, hKbound⟩ := exists_local_mode_integral_le b hbs
  refine ⟨8*K, by positivity, fun T S v c p q hp hpq hpHalf hidx hv hsep hb => ?_⟩
  let f (n : ℕ) := finiteModes T occurrenceFrequency (rootCoeff n)
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hp.trans_le hpq
  have hq0 : (0 : ℝ) < q := by linarith
  have hwidth : 1 / (q : ℝ) ≤ 1 := (div_le_one hq0).mpr hq₁
  have hsep' : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 / (q : ℝ) ≤ |v i-v j| := hsep
  have hbase : ∑ n ∈ S, ‖f p (v n)‖ ≤ 3*K*q := by
    have hU := hKbound T occurrenceFrequency (rootCoeff p) 2 (by norm_num)
      (occurrence_bin_majorant (by norm_num) hb (occurrence_coeff_le hRH hp₁)) c
    have hp0 : (0 : ℝ) < p := by linarith
    have hV := hKbound T occurrenceFrequency (phaseDerivCoeff occurrenceFrequency (rootCoeff p)) p hp0
      (occurrence_bin_majorant hp0.le hb (occurrence_coeff_phase_le hp0.le)) c
    have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
    calc
      _ ≤ K * 2 / (1/(q : ℝ)) + K * p :=
        separated_mode_samples_le (by positivity) hwidth hv hsep' hU hV
      _ ≤ _ := by
        rw [div_div_eq_mul_div, div_one]
        nlinarith only [mul_le_mul_of_nonneg_left hpq' hK.le]
  have hdiff : ∀ r ∈ Finset.Ico p q, ∑ n ∈ S, ‖f (r+1) (v n) - f r (v n)‖ ≤ 5*K := by
    intro r hr
    have hpr : (p : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Ico.mp hr).1
    have hr₁ := hp₁.trans hpr
    have hC : 0 < 4 / (q : ℝ) := by positivity
    have hU := hKbound T occurrenceFrequency (occurrenceIncrement r) (4/q) hC
      (occurrence_bin_majorant hC.le hb (occurrenceIncrement_le hRH hr₁ hq0 (hpHalf.trans hpr))) c
    have hV := hKbound T occurrenceFrequency (phaseDerivCoeff occurrenceFrequency (occurrenceIncrement r))
      1 (by norm_num) (occurrence_bin_majorant (by norm_num) hb (fun i =>
        (occurrenceIncrement_phase_le hRH hr₁ i).trans_eq (one_mul _).symm)) c
    calc
      _ = ∑ n ∈ S, ‖finiteModes T occurrenceFrequency (occurrenceIncrement r) (v n)‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        congr 1
        unfold f finiteModes occurrenceIncrement
        push_cast
        rw [← Finset.sum_sub_distrib]
        simp only [sub_mul]
      _ ≤ K * (4/(q : ℝ)) / (1/(q : ℝ)) + K * 1 :=
        separated_mode_samples_le (by positivity) hwidth hv hsep' hU hV
      _ = _ := by
        field_simp
        ring
  have hc : ((Finset.Ico p q).card : ℝ) ≤ q := by
    exact_mod_cast (show (Finset.Ico p q).card ≤ q by rw [Nat.card_Ico]; omega)
  exact (varying_sample_sum_le hidx hbase hdiff).trans (by
    nlinarith only [mul_le_mul_of_nonneg_right hc (show 0 ≤ 5*K by positivity)])

open D5.S3.Weil.ZeroSum
open scoped BigOperators Topology

private theorem band_coord_lower {k : ℤ} {γ : ℝ}
    (hγ : frequencyBin γ = k) : |(k : ℝ)| ≤ |γ| + 1 := by
  have hr := mem_frequencyBin γ
  rw [hγ] at hr
  rw [abs_le]
  exact ⟨by linarith only [hr.2, neg_abs_le γ], by linarith only [hr.1, le_abs_self γ]⟩

private theorem log_band_le (x : ℝ) (hx : 0 ≤ x) :
    Real.log (x+3) ≤ (Real.log 3 + 4) * (x+1) ^ (1/4 : ℝ) := by
  have hx1 : 1 ≤ x+1 := by linarith
  have hpow : 1 ≤ (x+1) ^ (1/4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (by linarith : 0 < x+1) (1/4 : ℝ))
  rw [Real.log_rpow (by linarith : 0 < x+1)] at hlog
  calc
    _ ≤ Real.log (3*(x+1)) := Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 3 + Real.log (x+1) := Real.log_mul (by norm_num) (by linarith)
    _ ≤ _ := by
      have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
      nlinarith only [hlog, mul_nonneg hl (sub_nonneg.mpr hpow)]

private theorem summable_band_rpow_sq (D : ℝ) :
    Summable fun k : ℤ => (D * (|(k : ℝ)|+1) ^ (-3/4 : ℝ))^2 := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3/2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have ht := (summable_nat_add_iff 1).2 hs
  have he (x : ℝ) (hx : 0 ≤ x) :
      (D * (x+1) ^ (-3/4 : ℝ))^2 = D^2 * (x+1)^(-3/2 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by linarith : 0 ≤ x+1)]
    norm_num
  rw [summable_int_iff_summable_nat_and_neg]
  have hn := (ht.mul_left (D^2))
  constructor <;> apply hn.congr <;> intro n <;>
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      Nat.cast_add, Nat.cast_one, he _ (Nat.cast_nonneg (α := ℝ) n)]

private theorem occurrence_bin_square_majorant (hRH : RiemannHypothesis) :
    ∃ b : ℤ → ℝ, (Summable fun k => b k^2) ∧
      ∀ (T : Finset ℕ) (k : ℤ),
        ∑ i ∈ T with frequencyBin (occurrenceFrequency i) = k, (‖actualZero i‖)⁻¹ ≤ b k := by
  classical
  obtain ⟨A, hA, hcount⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨fun k => (5*A*(Real.log 3+4)) * (|(k : ℝ)|+1)^(-3/4 : ℝ),
    summable_band_rpow_sq _, ?_⟩
  intro T k
  let W := Zeta23.zerosIn (k : ℝ) ((k : ℝ)+1)
  let F := (Zeta23.zerosIn_finite (k : ℝ) ((k : ℝ)+1)).toFinset
  let I := T.filter (fun i => frequencyBin (occurrenceFrequency i) = k)
  let f (i : ℕ) : ℝ := if actualZero i ∈ F then 1 else 0
  have hF (ρ : ℂ) : ρ ∈ F ↔ ρ ∈ W := Set.Finite.mem_toFinset _
  have hIS (i : ℕ) (hi : i ∈ I) : actualZero i ∈ F := by
    have hmem := mem_frequencyBin (occurrenceFrequency i)
    rw [(Finset.mem_filter.mp hi).2] at hmem
    exact (hF _).2 ⟨D5.S3.Weil.Mertens.ZeroAbscissaPower.actual_zero i, hmem⟩
  have hSN : (I.card : ℝ) ≤ (Zeta23.zetaZeroConfig.N k ((k : ℝ)+1) : ℝ) := by
    obtain ⟨hs, hsum⟩ := D5.S3.Weil.Mertens.ZeroAbscissaPower.occurrence_finite_sum F (fun ρ hρ => ((hF ρ).1 hρ).1)
      (fun _ => 1) (fun _ => zero_le_one)
    have hsum' : (∑' i : ℕ, f i) = (Zeta23.zetaZeroConfig.N k ((k : ℝ)+1) : ℝ) := by
      rw [hsum, Zeta23.zetaZeroConfig_N, Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _
        (Zeta23.zerosIn_finite (k : ℝ) ((k : ℝ)+1)), Nat.cast_sum]
      simp only [mul_one]
      rfl
    calc
      _ = ∑ i ∈ I, (1 : ℝ) := by simp [nsmul_eq_mul]
      _ = ∑ i ∈ I, f i := (Finset.sum_congr rfl (fun i hi => ite_eq_left (hIS i hi))).symm
      _ ≤ _ := (hs.sum_le_tsum I (fun i _ => by split_ifs <;> norm_num)).trans_eq hsum'
  have hb : ∀ i ∈ I, (‖actualZero i‖)⁻¹ ≤ 5 / (|(k : ℝ)|+1) := by
    intro i hi
    have h := band_coord_lower (Finset.mem_filter.mp hi).2
    have hhalf := Complex.abs_re_le_norm (actualZero i)
    rw [on_line hRH i] at hhalf
    norm_num at hhalf
    have him : |occurrenceFrequency i| ≤ ‖actualZero i‖ := Complex.abs_im_le_norm _
    have hnorm := occurrence_norm_pos hRH i
    rw [inv_eq_one_div, div_le_div_iff₀ hnorm (by positivity)]
    linarith only [h, hhalf, him]
  calc
    _ ≤ ∑ _i ∈ I, 5 / (|(k : ℝ)|+1) := Finset.sum_le_sum hb
    _ = (I.card : ℝ) * (5 / (|(k : ℝ)|+1)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ A * Real.log (|(k : ℝ)|+3) * (5 / (|(k : ℝ)|+1)) :=
      mul_le_mul_of_nonneg_right (hSN.trans (hcount k)) (by positivity)
    _ ≤ A * ((Real.log 3+4) * (|(k : ℝ)|+1)^(1/4 : ℝ)) * (5 / (|(k : ℝ)|+1)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (log_band_le _ (abs_nonneg _)) (by linarith)) (by positivity)
    _ = _ := by
      have hbase : 0 < |(k : ℝ)|+1 := by positivity
      dsimp only
      rw [show (-3/4 : ℝ) = 1/4 - 1 by norm_num, Real.rpow_sub hbase, Real.rpow_one]
      ring

private theorem root_coord_separated {u : ℝ} {q i j : ℕ} (hu : (q : ℝ) ≤ u)
    (hi : 0 < i) (hj : 0 < j) (hiq : i ≤ q) (hjq : j ≤ q) (hij : i ≠ j) :
    1/(q : ℝ) ≤ |u / (i : ℝ) - u / (j : ℝ)| := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hq : (0 : ℝ) < q := by exact_mod_cast hi.trans_le hiq
  have hiq' : (i : ℝ) ≤ q := by exact_mod_cast hiq
  have hjq' : (j : ℝ) ≤ q := by exact_mod_cast hjq
  have hd (hij' : i < j) :
      1/(q : ℝ) ≤ u/(i : ℝ)-u/(j : ℝ) := by
    have ht : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij'
    have hdiff : 1 ≤ (j : ℝ)-(i : ℝ) := by linarith
    rw [div_sub_div _ _ hi'.ne' hj'.ne']
    apply (div_le_div_iff₀ hq (mul_pos hi' hj')).mpr
    rw [show u * (j : ℝ) - (i : ℝ) * u = u * ((j : ℝ)-(i : ℝ)) by ring]
    calc
      1 * ((i : ℝ) * j) ≤ (q : ℝ) * q := by
        rw [one_mul]
        exact mul_le_mul hiq' hjq' hj'.le hq.le
      _ ≤ u * ((j : ℝ)-(i : ℝ)) * q := by
        exact mul_le_mul_of_nonneg_right (hu.trans (le_mul_of_one_le_right (hq.le.trans hu) hdiff)) hq.le
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact (hd hij').trans (le_abs_self _)
  · have ht : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji'
    have hdiff : 1 ≤ (i : ℝ)-(j : ℝ) := by linarith
    apply le_trans _ (neg_le_abs (u / (i : ℝ) - u / (j : ℝ)))
    rw [neg_sub, div_sub_div _ _ hj'.ne' hi'.ne']
    apply (div_le_div_iff₀ hq (mul_pos hj' hi')).mpr
    rw [show u * (i : ℝ) - (j : ℝ) * u = u * ((i : ℝ)-(j : ℝ)) by ring]
    simpa only [one_mul] using
      (mul_le_mul hjq' hiq' hi'.le hq.le).trans
        (mul_le_mul_of_nonneg_right (hu.trans (le_mul_of_one_le_right (hq.le.trans hu) hdiff)) hq.le)

private theorem occurrence_weighted_finite (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (_hq : 3 ≤ q) (u : ℝ), (q : ℝ) ≤ u →
      ∀ T : Finset ℕ, (∑ n ∈ Finset.Icc ((q+1)/2) q,
        Real.exp (-(2*u/(q : ℝ) - u/(n : ℝ))/2) *
          ‖finiteModes T occurrenceFrequency (rootCoeff n) (u/(n : ℝ))‖) ≤ K*q := by
  obtain ⟨b, hb, hmass⟩ := occurrence_bin_square_majorant hRH
  obtain ⟨C, hC, hband⟩ := occurrence_band_samples hRH hb
  let r := Real.exp (-1/2 : ℝ)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hgeom := summable_geometric_of_lt_one hr0.le hr1
  refine ⟨C/(1-r), div_pos hC (sub_pos.mpr hr1), fun q hq u hu T => ?_⟩
  let p := (q+1)/2
  let S := Finset.Icc p q
  let v (n : ℕ) := u/(n : ℝ)
  let t (n : ℕ) := 2*u/(q : ℝ)-v n
  let j (n : ℕ) := ⌊t n⌋₊
  let w (n : ℕ) := ‖finiteModes T occurrenceFrequency (rootCoeff n) (v n)‖
  let J := S.image j
  have hp : 0 < p := by dsimp [p]; omega
  have hpq : p ≤ q := by dsimp [p]; omega
  have hhalf : (q : ℝ) / 2 ≤ p := by
    have h : q ≤ 2*p := by dsimp [p]; omega
    have h' : (q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast h
    linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.trans_le hpq
  have hu0 : 0 ≤ u := hq0.le.trans hu
  have ht : ∀ n ∈ S, 0 ≤ t n := by
    intro n hn
    have hn' := (Finset.mem_Icc.mp hn).1
    have hx : (p : ℝ) ≤ n := by exact_mod_cast hn'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.trans_le hn'
    have hqhalf : (0 : ℝ) < (q : ℝ)/2 := by linarith
    have h := div_le_div_of_nonneg_left hu0 hqhalf (hhalf.trans hx)
    dsimp [t, v]
    rw [show u / ((q : ℝ)/2) = 2*u/(q : ℝ) by ring] at h
    linarith
  have hband' (k : ℕ) :
      ∑ n ∈ S with j n = k, w n ≤ C*q := by
    let center := 2*u/(q : ℝ) - (k : ℝ) - 1/2
    apply hband T (S.filter (j · = k)) v center p q hp hpq hhalf
      (fun n hn => (Finset.mem_filter.mp hn).1) ?_ ?_ (hmass T)
    · intro n hn
      obtain ⟨hnS, hnk⟩ := Finset.mem_filter.mp hn
      have h₁ := Nat.floor_le (ht n hnS)
      have h₂ := Nat.lt_floor_add_one (t n)
      change (j n : ℝ) ≤ t n at h₁
      change t n < (j n : ℝ) + 1 at h₂
      rw [hnk] at h₁ h₂
      dsimp [t] at h₁ h₂
      exact ⟨by dsimp [center]; linarith, by dsimp [center]; linarith⟩
    · intro n hn l hl hnl
      have hn' := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      have hl' := Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1
      exact root_coord_separated hu (hp.trans_le hn'.1) (hp.trans_le hl'.1) hn'.2 hl'.2 hnl
  change (∑ n ∈ S, Real.exp (-(t n)/2) * w n) ≤ C/(1-r) * q
  rw [← Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem j hn)
    (fun n => Real.exp (-(t n)/2) * w n)]
  calc
    _ ≤ ∑ k ∈ J, r^k * (C*q) := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ∑ n ∈ S with j n = k, r^k * w n := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨hnS, hnk⟩ := Finset.mem_filter.mp hn
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          dsimp only [r]
          rw [← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          have h₁ := Nat.floor_le (ht n hnS)
          change (j n : ℝ) ≤ t n at h₁
          rw [hnk] at h₁
          linarith
        _ ≤ _ := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hband' k) (pow_nonneg hr0.le _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      have hsum := hgeom.sum_le_tsum J (fun k _ => pow_nonneg hr0.le _)
      rw [tsum_geometric_of_lt_one hr0.le hr1] at hsum
      exact (mul_le_mul_of_nonneg_right hsum (by positivity)).trans_eq (by ring)

private theorem rootMode_eq_phase (hRH : RiemannHypothesis) {r : ℝ} (hr : 0 < r) (u : ℝ)
    (i : ℕ) : rootMode r u i =
      (Real.exp (((2*r)⁻¹-1/2)*u) : ℂ) *
        (rootCoeff r i * Complex.exp (Complex.I * (occurrenceFrequency i : ℂ) * ((u/r : ℝ) : ℂ))) := by
  have hzero : actualZero i = (1/2 : ℂ) + Complex.I * (occurrenceFrequency i : ℂ) := by
    apply Complex.ext
    · simp [on_line hRH i, Complex.mul_re]
    · simp [occurrenceFrequency, Complex.mul_im]
  rw [rootMode, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [hzero]
  push_cast
  field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne']
  ring

private theorem rootMode_phase_summable (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 ≤ r)
    (u : ℝ) : Summable (fun i => rootCoeff r i *
      Complex.exp (Complex.I * (occurrenceFrequency i : ℂ) * ((u/r : ℝ) : ℂ))) := by
  apply (actualCoeff_hasSum.summable.norm.mul_left r).of_norm_bounded
  intro i
  have hgap : ‖1 - actualZero i‖ ≤ ‖(r : ℂ) - actualZero i‖ := by
    have heq : ‖1 - actualZero i‖ = ‖actualZero i‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, on_line hRH i]
      ring
    exact heq.trans_le (occurrence_dist_norm hRH hr i)
  have hpos : 0 < ‖1 - actualZero i‖ := by
    have h := Complex.abs_re_le_norm (1 - actualZero i)
    rw [Complex.sub_re, Complex.one_re, on_line hRH i] at h
    norm_num at h
    linarith
  rw [norm_mul, Complex.norm_exp, show
      (Complex.I * (occurrenceFrequency i : ℂ) * ((u/r : ℝ) : ℂ)).re = 0 by
        simp [Complex.mul_re, Complex.mul_im], Real.exp_zero, mul_one]
  unfold rootCoeff actualCoeff
  simp only [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_one]
  rw [abs_of_nonneg (by linarith : 0 ≤ r), mul_one_div]
  exact div_le_div_of_nonneg_left (by linarith) (mul_pos (occurrence_norm_pos hRH i) hpos)
    (mul_le_mul_of_nonneg_left hgap (norm_nonneg _))

private theorem occurrence_weighted_infinite (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ), 3 ≤ q → ∀ (u : ℝ), (q : ℝ) ≤ u →
      (∑ n ∈ Finset.Icc ((q+1)/2) q,
        Real.exp (-(2*u/(q : ℝ) - u/(n : ℝ))/2) *
          ‖∑' i : ℕ, rootCoeff n i *
            Complex.exp (Complex.I * (occurrenceFrequency i : ℂ) * ((u/(n : ℝ) : ℝ) : ℂ))‖) ≤ K*q := by
  obtain ⟨K, hK, hfinite⟩ := occurrence_weighted_finite hRH
  refine ⟨K, hK, fun q hq u hu => ?_⟩
  let S := Finset.Icc ((q+1)/2) q
  let w (n : ℕ) := Real.exp (-(2*u/(q : ℝ) - u/(n : ℝ))/2)
  have hterm (n : ℕ) (hn : n ∈ S) := (rootMode_phase_summable hRH
    (r := (n : ℝ)) (by
      have h := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (show 1 ≤ n by omega)) u).hasSum.tendsto_sum_nat.norm.const_mul (w n)
  have hlim := tendsto_finsetSum S hterm
  exact le_of_tendsto' hlim (fun N => hfinite q hq u hu (Finset.range N))

theorem omitted_root_density_linear (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ), 2 ≤ m → ∀ (u : ℝ), (m : ℝ)+1 ≤ u →
      (∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n), |rootDensity n u|) ≤
        K * (m : ℝ) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨K, hK, hroot⟩ := occurrence_weighted_infinite hRH
  refine ⟨2*K, by positivity, fun m hm u hu => ?_⟩
  let q := m+1
  let P := (Finset.Icc 2 m).filter (fun n => q ≤ 2*n)
  let S := Finset.Icc ((q+1)/2) q
  let W := Real.exp (-(orderRate m)*u)
  let w (n : ℕ) := Real.exp (-(2*u/(q : ℝ) - u/(n : ℝ))/2)
  let f (n : ℕ) := ‖∑' i : ℕ, rootCoeff n i *
    Complex.exp (Complex.I * (occurrenceFrequency i : ℂ) * ((u/(n : ℝ) : ℝ) : ℂ))‖
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqu : (q : ℝ) ≤ u := by simpa [q] using hu
  have hsubset : P ⊆ S := by
    intro n hn
    obtain ⟨hnI, hnp⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn₂, hnm⟩ := Finset.mem_Icc.mp hnI
    exact Finset.mem_Icc.mpr ⟨by omega, by dsimp [q]; omega⟩
  have hbound : ∀ n ∈ P, |rootDensity n u| ≤ W * (w n * f n) := by
    intro n hn
    have hn₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    unfold rootDensity
    apply (Complex.abs_re_le_norm _).trans
    simp_rw [rootMode_eq_phase hRH hn0 u]
    rw [tsum_mul_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have he : Real.exp (((2*(n : ℝ))⁻¹-1/2)*u) = W * w n := by
      dsimp [W, w, orderRate, q]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, mul_assoc]
  change (∑ n ∈ P, |rootDensity n u|) ≤ 2*K*(m : ℝ)*W
  calc
    _ ≤ W * ∑ n ∈ P, w n * f n := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hbound
    _ ≤ W * ∑ n ∈ S, w n * f n := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _ _ => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
    _ ≤ W * (K*q) := mul_le_mul_of_nonneg_left (hroot q hq u hqu) (Real.exp_nonneg _)
    _ ≤ _ := by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      have hq' : (q : ℝ) ≤ 2*(m : ℝ) := by simp [q]; linarith
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq' hK.le)
        (Real.exp_nonneg _)).trans_eq (by ring)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
