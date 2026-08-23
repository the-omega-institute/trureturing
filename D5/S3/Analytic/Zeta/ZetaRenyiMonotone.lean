/- GID: D5/S3/Analytic/Zeta/ZetaRenyiMonotone
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The zeta law's Renyi entropy is antitone on each side of order one. -/

import Mathlib
/- Provenance: Native proof over pinned mathlib. -/
import D5.S3.Analytic.Zeta.ZetaRenyiEntropy

/-!
Library-search audit (2026-08-23): searches of pinned mathlib for `Renyi`, `powerMean`,
`rpow.*tsum`, `Convex.*tsum`, `map_tsum`, `Holder.*tsum`, and the finite weighted Jensen lemma
found no Renyi-entropy theorem and no countable weighted Jensen theorem.  Mathlib does provide the
finite Jensen theorem `Real.rpow_arith_mean_le_arith_mean_rpow` and, more directly useful here,
the countable Holder theorem `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg`.  The latter proves the
power-sum interpolation used below without finite truncations.

Order one is deliberately absent.  The repository's totalized definition has
`countableRenyiEntropy 1 p = 0`, so the literal function has a downward spike there and cannot be
antitone on an interval containing one.  Below one the hypothesis `1 < alpha * s` is exactly the
p-series summability condition at the smaller order; monotonicity and `0 < s` then give it at
`beta`.  Above one, `1 < s` and `1 < alpha` imply both required summability conditions.
-/

namespace D5.S3.Analytic.Zeta.ZetaRenyiMonotone

open scoped ENNReal BigOperators
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.ZetaRenyiEntropy

noncomputable section

private lemma power_sum_interpolate (p : PMF ℕ) (a t : ℝ)
    (ha : 0 < a) (ht : 0 < t) (ht_one : t < 1)
    (hsum : Summable (fun n => (pmfReal p n) ^ a)) :
    (∑' n, (pmfReal p n) ^ (t * a + (1 - t))) ≤
      (∑' n, (pmfReal p n) ^ a) ^ t := by
  have hp_nonneg (n : ℕ) : 0 ≤ pmfReal p n := ENNReal.toReal_nonneg
  have htail : 0 < 1 - t := sub_pos.mpr ht_one
  have hconj : t⁻¹.HolderConjugate (1 - t)⁻¹ := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact (one_lt_inv₀ ht).2 ht_one
    · simp
  have hf_sum : Summable (fun n => ((pmfReal p n) ^ (a * t)) ^ t⁻¹) := by
    convert hsum using 1
    funext n
    rw [← Real.rpow_mul (hp_nonneg n)]
    congr 1
    field_simp
  have hg_sum : Summable (fun n => ((pmfReal p n) ^ (1 - t)) ^ (1 - t)⁻¹) := by
    convert pmfReal_summable p using 1
    funext n
    rw [← Real.rpow_mul (hp_nonneg n)]
    field_simp
    rw [Real.rpow_one]
  have hholder := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hconj
    (fun n => Real.rpow_nonneg (hp_nonneg n) (a * t))
    (fun n => Real.rpow_nonneg (hp_nonneg n) (1 - t)) hf_sum hg_sum
  have hterm (n : ℕ) :
      (pmfReal p n) ^ (a * t) * (pmfReal p n) ^ (1 - t) =
        (pmfReal p n) ^ (t * a + (1 - t)) := by
    by_cases hn : pmfReal p n = 0
    · have hat : 0 < a * t := mul_pos ha ht
      have htotal : 0 < t * a + (1 - t) := by positivity
      simp [hn, Real.zero_rpow hat.ne', Real.zero_rpow htail.ne',
        Real.zero_rpow htotal.ne']
    · have hn_pos : 0 < pmfReal p n := lt_of_le_of_ne (hp_nonneg n) (Ne.symm hn)
      rw [← Real.rpow_add hn_pos]
      congr 1
      ring
  rw [show (fun n => (pmfReal p n) ^ (t * a + (1 - t))) =
      fun n => (pmfReal p n) ^ (a * t) * (pmfReal p n) ^ (1 - t) by
        funext n
        exact (hterm n).symm]
  calc
    (∑' n, (pmfReal p n) ^ (a * t) * (pmfReal p n) ^ (1 - t)) ≤
        (∑' n, ((pmfReal p n) ^ (a * t)) ^ t⁻¹) ^ (1 / t⁻¹) *
          (∑' n, ((pmfReal p n) ^ (1 - t)) ^ (1 - t)⁻¹) ^
            (1 / (1 - t)⁻¹) := hholder
    _ = (∑' n, (pmfReal p n) ^ a) ^ t := by
      rw [show (fun n => ((pmfReal p n) ^ (a * t)) ^ t⁻¹) =
          fun n => (pmfReal p n) ^ a by
            funext n
            rw [← Real.rpow_mul (hp_nonneg n)]
            congr 1
            field_simp,
        show (fun n => ((pmfReal p n) ^ (1 - t)) ^ (1 - t)⁻¹) =
          pmfReal p by
            funext n
            rw [← Real.rpow_mul (hp_nonneg n)]
            field_simp
            rw [Real.rpow_one],
        tsum_pmfReal]
      field_simp
      simp

private lemma zeta_power_sum_pos (s gamma : ℝ) (hs : 1 < s)
    (hgamma_s : 1 < gamma * s) :
    0 < ∑' n, (pmfReal (zetaDist s hs) n) ^ gamma := by
  have hsum := zeta_renyi_power_summable s gamma hs hgamma_s
  have hone : 0 < (pmfReal (zetaDist s hs) 1) ^ gamma :=
    Real.rpow_pos_of_pos (zeta_real_pos s hs (by norm_num)) gamma
  exact lt_of_lt_of_le (by simpa using hone)
    (hsum.sum_le_tsum {1} (fun n _ => Real.rpow_nonneg ENNReal.toReal_nonneg gamma))

/-- For a zeta law, Renyi entropy is non-increasing between convergent orders below one.
`1 < alpha * s` is the exact power-sum convergence condition at the smaller order; `alpha ≤ beta`
then supplies convergence at the larger order.  The strict upper bound excludes the totalized
order-one value, which is zero rather than the Shannon-limit value. -/
theorem zeta_renyi_entropy_antitone_of_lt_one (s alpha beta : ℝ) (hs : 1 < s)
    (halpha_s : 1 < alpha * s) (horder : alpha ≤ beta ∧ beta < 1) :
    countableRenyiEntropy beta (zetaDist s hs) ≤
      countableRenyiEntropy alpha (zetaDist s hs) := by
  rcases horder with ⟨hab, hbeta_one⟩
  rcases hab.eq_or_lt with rfl | hab_lt
  · rfl
  have hs_pos : 0 < s := lt_trans (by norm_num) hs
  have halpha_pos : 0 < alpha := by nlinarith
  have halpha_one : alpha < 1 := hab_lt.trans hbeta_one
  have halpha_den : 1 - alpha ≠ 0 := sub_ne_zero.mpr (ne_of_gt halpha_one)
  have hbeta_den : 1 - beta ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbeta_one)
  have hbeta_s : 1 < beta * s := by nlinarith
  let t := (1 - beta) / (1 - alpha)
  have ht : 0 < t := div_pos (sub_pos.mpr hbeta_one) (sub_pos.mpr halpha_one)
  have ht_one : t < 1 := (div_lt_one (sub_pos.mpr halpha_one)).2 (by linarith)
  have hexp : t * alpha + (1 - t) = beta := by
    dsimp [t]
    field_simp [halpha_den]
    ring
  have hinterp :
      (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) ≤
        (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) ^ t := by
    rw [← hexp]
    exact power_sum_interpolate (zetaDist s hs) alpha t halpha_pos ht ht_one
      (zeta_renyi_power_summable s alpha hs halpha_s)
  have hsum_alpha := zeta_power_sum_pos s alpha hs halpha_s
  have hsum_beta := zeta_power_sum_pos s beta hs hbeta_s
  have hlog :
      Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) ≤
        t * Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) := by
    calc
      Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) ≤
          Real.log ((∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) ^ t) :=
        Real.log_le_log hsum_beta hinterp
      _ = t * Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) :=
        Real.log_rpow hsum_alpha t
  rw [countableRenyiEntropy, countableRenyiEntropy]
  calc
    (1 / (1 - beta)) * Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) =
        Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) / (1 - beta) := by ring
    _ ≤ (t * Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha)) /
        (1 - beta) := (div_le_div_iff_of_pos_right (sub_pos.mpr hbeta_one)).2 hlog
    _ = Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) / (1 - alpha) := by
      dsimp [t]
      field_simp [hbeta_den, halpha_den]
    _ = (1 / (1 - alpha)) *
        Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) := by ring

/-- For a zeta law, Renyi entropy is non-increasing between orders strictly above one.
Here `1 < s` and `1 < alpha ≤ beta` already imply convergence of both power sums.  Staying
strictly above one fixes the negative sign of `1 - order` and avoids the totalized singularity. -/
theorem zeta_renyi_entropy_antitone_of_one_lt (s alpha beta : ℝ) (hs : 1 < s)
    (horder : 1 < alpha ∧ alpha ≤ beta) :
    countableRenyiEntropy beta (zetaDist s hs) ≤
      countableRenyiEntropy alpha (zetaDist s hs) := by
  rcases horder with ⟨halpha_one, hab⟩
  rcases hab.eq_or_lt with rfl | hab_lt
  · rfl
  have hs_pos : 0 < s := lt_trans (by norm_num) hs
  have hbeta_one : 1 < beta := halpha_one.trans hab_lt
  have halpha_sub_ne : alpha - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt halpha_one)
  have hbeta_sub_ne : beta - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbeta_one)
  have hone_alpha_ne : 1 - alpha ≠ 0 := sub_ne_zero.mpr (ne_of_lt halpha_one)
  have hone_beta_ne : 1 - beta ≠ 0 := sub_ne_zero.mpr (ne_of_lt hbeta_one)
  have halpha_s : 1 < alpha * s := by nlinarith
  have hbeta_s : 1 < beta * s := by nlinarith
  let t := (alpha - 1) / (beta - 1)
  have ht : 0 < t := div_pos (sub_pos.mpr halpha_one) (sub_pos.mpr hbeta_one)
  have ht_one : t < 1 := (div_lt_one (sub_pos.mpr hbeta_one)).2 (by linarith)
  have hexp : t * beta + (1 - t) = alpha := by
    dsimp [t]
    field_simp [hbeta_sub_ne]
    ring
  have hinterp :
      (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) ≤
        (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) ^ t := by
    rw [← hexp]
    exact power_sum_interpolate (zetaDist s hs) beta t (by linarith) ht ht_one
      (zeta_renyi_power_summable s beta hs hbeta_s)
  have hsum_alpha := zeta_power_sum_pos s alpha hs halpha_s
  have hsum_beta := zeta_power_sum_pos s beta hs hbeta_s
  have hlog :
      Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) ≤
        t * Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) := by
    calc
      Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) ≤
          Real.log ((∑' n, (pmfReal (zetaDist s hs) n) ^ beta) ^ t) :=
        Real.log_le_log hsum_alpha hinterp
      _ = t * Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) :=
        Real.log_rpow hsum_beta t
  have hratio :
      Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) / (alpha - 1) ≤
        Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) / (beta - 1) := by
    calc
      Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) / (alpha - 1) ≤
          (t * Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta)) /
            (alpha - 1) :=
        (div_le_div_iff_of_pos_right (sub_pos.mpr halpha_one)).2 hlog
      _ = Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) / (beta - 1) := by
        dsimp [t]
        field_simp [halpha_sub_ne, hbeta_sub_ne]
  rw [countableRenyiEntropy, countableRenyiEntropy]
  calc
    (1 / (1 - beta)) * Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) =
        -(Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ beta) / (beta - 1)) := by
      field_simp [hone_beta_ne, hbeta_sub_ne]
      ring
    _ ≤ -(Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) / (alpha - 1)) :=
      neg_le_neg hratio
    _ = (1 / (1 - alpha)) *
        Real.log (∑' n, (pmfReal (zetaDist s hs) n) ^ alpha) := by
      field_simp [hone_alpha_ne, halpha_sub_ne]
      ring

end

end D5.S3.Analytic.Zeta.ZetaRenyiMonotone
