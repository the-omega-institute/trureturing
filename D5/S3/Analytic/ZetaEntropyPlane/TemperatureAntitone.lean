/- GID: D5/S3/Analytic/ZetaEntropyPlane/TemperatureAntitone
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeta Renyi entropy decreases with inverse temperature and obeys reciprocal-order duality. -/

import Mathlib
/- Provenance: Native proof over pinned mathlib. -/
import D5.S3.Analytic.Zeta.ZetaRenyiEntropy

/-!
Search receipt (2026-08-23): repository-wide searches for `countableEntropy`,
`countableRenyiEntropy`, `Monotone`, and `Antitone` found order monotonicity and temperature-limit
results, but no entropy monotonicity in the temperature parameter.  Searches of pinned mathlib for
zeta monotonicity, log-convex sums, covariance, and Holder machinery found no ready-made zeta
result.  The countable Holder inequality
`Real.inner_le_Lp_mul_Lq_tsum_of_nonneg` supplies the log-convexity argument below.

The temperature theorem uses only `1 < s`, convergence at the initial endpoint
`1 < alpha * s`, and `s <= t`: these imply positivity of `alpha` and convergence at `t`.
Order one is included because the repository's totalized Renyi expression is exactly zero there.
The reciprocal-order identity has the same two convergence inequalities after substitution; its
proof is separate and is not used for temperature monotonicity.
-/

namespace D5.S3.Analytic.ZetaEntropyPlane.TemperatureAntitone

open scoped ENNReal BigOperators
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.ZetaRenyiEntropy

noncomputable section

private def logPartition (s : ℝ) : ℝ :=
  Real.log (partitionFunction s).toReal

private lemma logPartition_convex_combo (x y a b : ℝ) (hx : 1 < x) (hy : 1 < y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    logPartition (a * x + b * y) <= a * logPartition x + b * logPartition y := by
  have hmix : 1 < a * x + b * y := by nlinarith
  have hconj : a⁻¹.HolderConjugate b⁻¹ :=
    Real.HolderConjugate.inv_inv ha hb hab
  have hfa : Summable (fun n : ℕ => ((n : ℝ) ^ (-(a * x))) ^ a⁻¹) := by
    convert summable_real_weight x hx using 1
    funext n
    rw [← Real.rpow_mul n.cast_nonneg]
    congr 1
    field_simp [ha.ne']
  have hfb : Summable (fun n : ℕ => ((n : ℝ) ^ (-(b * y))) ^ b⁻¹) := by
    convert summable_real_weight y hy using 1
    funext n
    rw [← Real.rpow_mul n.cast_nonneg]
    congr 1
    field_simp [hb.ne']
  have hholder := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hconj
    (fun n : ℕ => Real.rpow_nonneg n.cast_nonneg (-(a * x)))
    (fun n : ℕ => Real.rpow_nonneg n.cast_nonneg (-(b * y))) hfa hfb
  have hterm (n : ℕ) :
      (n : ℝ) ^ (-(a * x)) * (n : ℝ) ^ (-(b * y)) =
        (n : ℝ) ^ (-(a * x + b * y)) := by
    rcases n.eq_zero_or_pos with rfl | hn
    · have hax : -(a * x) < 0 := by
        have hx_pos : 0 < x := zero_lt_one.trans hx
        nlinarith [mul_pos ha hx_pos]
      have hby : -(b * y) < 0 := by
        have hy_pos : 0 < y := zero_lt_one.trans hy
        nlinarith [mul_pos hb hy_pos]
      have htotal : -(a * x + b * y) < 0 := by linarith
      norm_num only [Nat.cast_zero]
      rw [Real.zero_rpow hax.ne, Real.zero_rpow hby.ne, Real.zero_rpow htotal.ne,
        zero_mul]
    · have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      rw [← Real.rpow_add hnR]
      congr 1
      ring
  have hsum :
      (partitionFunction (a * x + b * y)).toReal <=
        (partitionFunction x).toReal ^ a * (partitionFunction y).toReal ^ b := by
    rw [← tsum_real_weight_eq_partition_toReal _ hmix,
      ← tsum_real_weight_eq_partition_toReal x hx,
      ← tsum_real_weight_eq_partition_toReal y hy]
    simp_rw [hterm] at hholder
    rw [show (fun n : ℕ => ((n : ℝ) ^ (-(a * x))) ^ a⁻¹) =
        fun n : ℕ => (n : ℝ) ^ (-x) by
          funext n
          rw [← Real.rpow_mul n.cast_nonneg]
          congr 1
          field_simp [ha.ne'],
      show (fun n : ℕ => ((n : ℝ) ^ (-(b * y))) ^ b⁻¹) =
        fun n : ℕ => (n : ℝ) ^ (-y) by
          funext n
          rw [← Real.rpow_mul n.cast_nonneg]
          congr 1
          field_simp [hb.ne']] at hholder
    have ha_inv : 1 / a⁻¹ = a := by field_simp [ha.ne']
    have hb_inv : 1 / b⁻¹ = b := by field_simp [hb.ne']
    simpa only [ha_inv, hb_inv] using hholder
  have hZx := partition_toReal_pos x hx
  have hZy := partition_toReal_pos y hy
  have hZmix := partition_toReal_pos (a * x + b * y) hmix
  calc
    logPartition (a * x + b * y) <=
        Real.log ((partitionFunction x).toReal ^ a *
          (partitionFunction y).toReal ^ b) :=
      Real.log_le_log hZmix hsum
    _ = a * logPartition x + b * logPartition y := by
      rw [Real.log_mul (Real.rpow_pos_of_pos hZx a).ne'
        (Real.rpow_pos_of_pos hZy b).ne', Real.log_rpow hZx, Real.log_rpow hZy]
      rfl

private lemma logPartition_convex :
    ConvexOn ℝ (Set.Ioi 1) logPartition := by
  rw [convexOn_iff_forall_pos]
  refine ⟨convex_Ioi 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa only [smul_eq_mul] using logPartition_convex_combo x y a b hx hy ha hb hab

private lemma logPartition_scaled_increment_of_one_lt (alpha s t : ℝ)
    (halpha : 1 < alpha) (hs : 1 < s) (hst : s < t) :
    alpha * (logPartition t - logPartition s) <=
      logPartition (alpha * t) - logPartition (alpha * s) := by
  have halpha_pos : 0 < alpha := zero_lt_one.trans halpha
  have ht : 1 < t := hs.trans hst
  have has : 1 < alpha * s := by nlinarith
  have hat : 1 < alpha * t := by nlinarith
  have hst_ne : t ≠ s := hst.ne'
  have hats_ne : alpha * t ≠ s := by nlinarith
  have hsat_ne : s ≠ alpha * t := by nlinarith
  have hast_ne : alpha * s ≠ alpha * t := by nlinarith
  have h₁ := logPartition_convex.secant_mono (a := s) (x := t) (y := alpha * t)
    hs ht hat hst_ne hats_ne (by nlinarith)
  have h₂ := logPartition_convex.secant_mono (a := alpha * t) (x := s)
    (y := alpha * s) hat hs has hsat_ne hast_ne (by nlinarith)
  have h₂' :
      (logPartition (alpha * t) - logPartition s) / (alpha * t - s) <=
        (logPartition (alpha * t) - logPartition (alpha * s)) /
          (alpha * t - alpha * s) := by
    have heq₁ :
        (logPartition (alpha * t) - logPartition s) / (alpha * t - s) =
          (logPartition s - logPartition (alpha * t)) / (s - alpha * t) := by
      field_simp [sub_ne_zero.mpr hats_ne, sub_ne_zero.mpr hsat_ne]
      ring
    have heq₂ :
        (logPartition (alpha * t) - logPartition (alpha * s)) /
            (alpha * t - alpha * s) =
          (logPartition (alpha * s) - logPartition (alpha * t)) /
            (alpha * s - alpha * t) := by
      field_simp [sub_ne_zero.mpr hast_ne, sub_ne_zero.mpr hast_ne.symm]
      ring
    rw [heq₁, heq₂]
    exact h₂
  have hslopes :
      (logPartition t - logPartition s) / (t - s) <=
        (logPartition (alpha * t) - logPartition (alpha * s)) /
          (alpha * t - alpha * s) := by
    calc
      (logPartition t - logPartition s) / (t - s) <=
          (logPartition (alpha * t) - logPartition s) / (alpha * t - s) := h₁
      _ <= (logPartition (alpha * t) - logPartition (alpha * s)) /
          (alpha * t - alpha * s) := h₂'
  have hdt : 0 < t - s := sub_pos.mpr hst
  have hscaled :
      (logPartition t - logPartition s) / (t - s) <=
        ((logPartition (alpha * t) - logPartition (alpha * s)) / alpha) /
          (t - s) := by
    calc
      _ <= (logPartition (alpha * t) - logPartition (alpha * s)) /
          (alpha * t - alpha * s) := hslopes
      _ = _ := by field_simp [halpha_pos.ne']
  have hdiv := (div_le_div_iff_of_pos_right hdt).mp hscaled
  simpa only [mul_comm] using (le_div_iff₀ halpha_pos).mp hdiv

private lemma logPartition_scaled_increment_of_lt_one (alpha s t : ℝ)
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1) (halpha_s : 1 < alpha * s)
    (hst : s < t) :
    logPartition (alpha * t) - logPartition (alpha * s) <=
      alpha * (logPartition t - logPartition s) := by
  have hs : 1 < s := lt_trans halpha_s (by nlinarith)
  have ht : 1 < t := hs.trans hst
  have hat : 1 < alpha * t := by nlinarith
  have hast_ne : alpha * t ≠ alpha * s := by nlinarith
  have hts_ne : t ≠ alpha * s := by nlinarith
  have hat_ne : alpha * t ≠ t := by nlinarith
  have hs_ne : alpha * s ≠ t := by nlinarith
  have h₁ := logPartition_convex.secant_mono (a := alpha * s) (x := alpha * t)
    (y := t) halpha_s hat ht hast_ne hts_ne (by nlinarith)
  have h₂ := logPartition_convex.secant_mono (a := t) (x := alpha * s) (y := s)
    ht halpha_s hs hs_ne hst.ne (by nlinarith)
  have h₂' :
      (logPartition t - logPartition (alpha * s)) / (t - alpha * s) <=
        (logPartition t - logPartition s) / (t - s) := by
    have heq₁ :
        (logPartition t - logPartition (alpha * s)) / (t - alpha * s) =
          (logPartition (alpha * s) - logPartition t) / (alpha * s - t) := by
      field_simp [sub_ne_zero.mpr hts_ne, sub_ne_zero.mpr hs_ne]
      ring
    have heq₂ :
        (logPartition t - logPartition s) / (t - s) =
          (logPartition s - logPartition t) / (s - t) := by
      field_simp [sub_ne_zero.mpr hst.ne', sub_ne_zero.mpr hst.ne]
      ring
    rw [heq₁, heq₂]
    exact h₂
  have hslopes :
      (logPartition (alpha * t) - logPartition (alpha * s)) /
          (alpha * t - alpha * s) <=
        (logPartition t - logPartition s) / (t - s) := by
    calc
      (logPartition (alpha * t) - logPartition (alpha * s)) /
          (alpha * t - alpha * s) <=
          (logPartition t - logPartition (alpha * s)) / (t - alpha * s) := h₁
      _ <= (logPartition t - logPartition s) / (t - s) := h₂'
  have hdt : 0 < t - s := sub_pos.mpr hst
  have hscaled :
      ((logPartition (alpha * t) - logPartition (alpha * s)) / alpha) /
          (t - s) <=
        (logPartition t - logPartition s) / (t - s) := by
    calc
      _ = (logPartition (alpha * t) - logPartition (alpha * s)) /
          (alpha * t - alpha * s) := by field_simp [halpha_pos.ne']
      _ <= _ := hslopes
  have hdiv := (div_le_div_iff_of_pos_right hdt).mp hscaled
  simpa only [mul_comm] using (div_le_iff₀ halpha_pos).mp hdiv

private lemma zeta_renyi_entropy_eq_logPartition (s alpha : ℝ) (hs : 1 < s)
    (halpha_ne_one : alpha ≠ 1) (halpha_s : 1 < alpha * s) :
    countableRenyiEntropy alpha (zetaDist s hs) =
      (1 / (1 - alpha)) * (logPartition (alpha * s) - alpha * logPartition s) := by
  rw [zeta_renyi_entropy_eq s alpha hs halpha_ne_one halpha_s]
  rw [← partition_toReal_eq_zeta_re (alpha * s) halpha_s,
    ← partition_toReal_eq_zeta_re s hs]
  have hZs := partition_toReal_pos s hs
  have hZas := partition_toReal_pos (alpha * s) halpha_s
  rw [Real.log_div hZas.ne' (Real.rpow_pos_of_pos hZs alpha).ne',
    Real.log_rpow hZs alpha]
  rfl

/-- At every convergent Renyi order, raising inverse temperature cannot increase the zeta law's
Renyi entropy.  The initial endpoint hypotheses imply all domain facts at `t`. -/
theorem zeta_renyi_entropy_temperature_antitone (alpha s t : ℝ) (hs : 1 < s)
    (halpha_s : 1 < alpha * s) (hst : s <= t) :
    countableRenyiEntropy alpha (zetaDist t (hs.trans_le hst)) <=
      countableRenyiEntropy alpha (zetaDist s hs) := by
  rcases hst.eq_or_lt with rfl | hst
  · rfl
  by_cases halpha_one : alpha = 1
  · subst alpha
    simp [countableRenyiEntropy]
  have halpha_pos : 0 < alpha := by nlinarith
  have ht : 1 < t := hs.trans hst
  have halpha_t : 1 < alpha * t := by nlinarith
  rw [zeta_renyi_entropy_eq_logPartition t alpha ht halpha_one halpha_t,
    zeta_renyi_entropy_eq_logPartition s alpha hs halpha_one halpha_s]
  rcases lt_or_gt_of_ne halpha_one with halpha_lt | halpha_gt
  · have hinc := logPartition_scaled_increment_of_lt_one alpha s t halpha_pos halpha_lt
      halpha_s hst
    have hcore :
        logPartition (alpha * t) - alpha * logPartition t <=
          logPartition (alpha * s) - alpha * logPartition s := by linarith
    exact mul_le_mul_of_nonneg_left hcore (by positivity)
  · have hinc := logPartition_scaled_increment_of_one_lt alpha s t halpha_gt hs hst
    have hcore :
        logPartition (alpha * s) - alpha * logPartition s <=
          logPartition (alpha * t) - alpha * logPartition t := by linarith
    exact mul_le_mul_of_nonpos_left hcore (by
      simpa only [one_div] using
        inv_nonpos.mpr (sub_nonpos.mpr halpha_gt.le))

/-- Reciprocal Renyi order and scaled inverse temperature leave the zeta entropy unchanged. -/
theorem zeta_renyi_entropy_reciprocal_temperature (alpha s : ℝ) (hs : 1 < s)
    (halpha_s : 1 < alpha * s) :
    countableRenyiEntropy alpha (zetaDist s hs) =
      countableRenyiEntropy alpha⁻¹ (zetaDist (alpha * s) halpha_s) := by
  by_cases halpha_one : alpha = 1
  · subst alpha
    simp [countableRenyiEntropy]
  have halpha_pos : 0 < alpha := by nlinarith
  have halpha_ne_zero : alpha ≠ 0 := halpha_pos.ne'
  have hinv_ne_one : alpha⁻¹ ≠ 1 := by
    intro h
    apply halpha_one
    field_simp [halpha_ne_zero] at h
    exact h.symm
  have hback : 1 < alpha⁻¹ * (alpha * s) := by
    convert hs using 1
    field_simp [halpha_ne_zero]
  rw [zeta_renyi_entropy_eq_logPartition s alpha hs halpha_one halpha_s,
    zeta_renyi_entropy_eq_logPartition (alpha * s) alpha⁻¹ halpha_s hinv_ne_one hback]
  have harg : alpha⁻¹ * (alpha * s) = s := by field_simp [halpha_ne_zero]
  rw [harg]
  field_simp [halpha_ne_zero, halpha_one]
  ring

end

end D5.S3.Analytic.ZetaEntropyPlane.TemperatureAntitone
