/- GID: D5/S3/Analytic/Zeta/ZetaMinEntropy
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Min-entropy of the zeta law and its infinite-order Renyi endpoint. -/

import D5.S3.Analytic.Zeta.ZetaRenyiEntropy

/- Provenance: Native proof over pinned mathlib.

Search receipt (2026-08-22): the repository and pinned mathlib contain no min-entropy API.
`LSeries.tendsto_atTop`, `LSeries.abscissaOfAbsConv_one`, and
`LSeries_one_eq_riemannZeta` supply the zeta-at-infinity limit.
`Real.rpow_le_one_of_one_le_of_nonpos` supplies the maximum-mass bound, while `ciSup_le` and
`le_ciSup` identify the attained supremum. -/

namespace D5.S3.Analytic.Zeta.ZetaMinEntropy

open Filter
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.ZetaRenyiEntropy

noncomputable section

/-- Countable min-entropy in nats: the negative logarithm of the largest point mass. -/
def countableMinEntropy (p : PMF ℕ) : ℝ :=
  -Real.log (⨆ n, pmfReal p n)

private lemma zeta_mass_le_one_mass (s : ℝ) (hs : 1 < s) (n : ℕ) :
    pmfReal (zetaDist s hs) n ≤ pmfReal (zetaDist s hs) 1 := by
  rw [zeta_real_apply, zeta_real_apply]
  simp only [Nat.cast_one, Real.one_rpow, one_mul]
  have hpow : (n : ℝ) ^ (-s) ≤ 1 := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [Real.zero_rpow (by linarith : -s ≠ 0)]
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr (partition_toReal_pos s hs).le)

private lemma zeta_iSup_pmfReal (s : ℝ) (hs : 1 < s) :
    (⨆ n, pmfReal (zetaDist s hs) n) = pmfReal (zetaDist s hs) 1 := by
  have hbdd : BddAbove (Set.range (pmfReal (zetaDist s hs))) := by
    refine ⟨pmfReal (zetaDist s hs) 1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact zeta_mass_le_one_mass s hs n
  apply le_antisymm
  · exact ciSup_le (zeta_mass_le_one_mass s hs)
  · exact le_ciSup hbdd 1

/-- The zeta law's largest atom is at `1`, so its min-entropy is `log ζ(s)`. -/
theorem zeta_min_entropy_eq (s : ℝ) (hs : 1 < s) :
    countableMinEntropy (zetaDist s hs) = Real.log (riemannZeta (s : ℂ)).re := by
  rw [countableMinEntropy, zeta_iSup_pmfReal, zeta_real_apply]
  simp only [Nat.cast_one, Real.one_rpow, one_mul, Real.log_inv]
  rw [partition_toReal_eq_zeta_re s hs]
  ring

private lemma riemannZeta_re_tendsto_one_atTop :
    Tendsto (fun x : ℝ ↦ (riemannZeta (x : ℂ)).re) atTop (nhds 1) := by
  have habscissa : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact EReal.coe_lt_top 1
  have hL : Tendsto (fun x : ℝ ↦ LSeries (1 : ℕ → ℂ) x) atTop (nhds (1 : ℂ)) := by
    simpa using LSeries.tendsto_atTop habscissa
  have heq : (fun x : ℝ ↦ LSeries (1 : ℕ → ℂ) x) =ᶠ[atTop]
      (fun x : ℝ ↦ riemannZeta (x : ℂ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact LSeries_one_eq_riemannZeta (by simpa using hx)
  have hzeta : Tendsto (fun x : ℝ ↦ riemannZeta (x : ℂ)) atTop (nhds (1 : ℂ)) :=
    hL.congr' heq
  convert! (Complex.continuous_re.tendsto (1 : ℂ)).comp hzeta using 1

/-- The Renyi entropies of the zeta law converge at infinite order to its min-entropy.

No pointwise `alpha ≠ 1` or convergence hypothesis is needed: along `atTop`, both
`1 < alpha` and `1 < alpha * s` hold eventually, exactly where the imported closed form applies. -/
theorem zeta_renyi_entropy_tendsto_min_entropy (s : ℝ) (hs : 1 < s) :
    Tendsto (fun alpha : ℝ ↦ countableRenyiEntropy alpha (zetaDist s hs)) atTop
      (nhds (countableMinEntropy (zetaDist s hs))) := by
  have hs_pos : 0 < s := zero_lt_one.trans hs
  have hscale : Tendsto (fun alpha : ℝ ↦ alpha * s) atTop atTop :=
    tendsto_id.atTop_mul_const hs_pos
  have hzeta : Tendsto (fun alpha : ℝ ↦
      (riemannZeta ((alpha * s : ℝ) : ℂ)).re) atTop (nhds 1) :=
    riemannZeta_re_tendsto_one_atTop.comp hscale
  have hzeta_log : Tendsto (fun alpha : ℝ ↦
      Real.log (riemannZeta ((alpha * s : ℝ) : ℂ)).re) atTop (nhds 0) := by
    simpa using hzeta.log one_ne_zero
  have hden : Tendsto (fun alpha : ℝ ↦ alpha - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  let Z : ℝ := (riemannZeta (s : ℂ)).re
  have hZ_pos : 0 < Z := by
    dsimp [Z]
    rw [← partition_toReal_eq_zeta_re s hs]
    exact partition_toReal_pos s hs
  have hsmall : Tendsto (fun alpha : ℝ ↦
      Real.log Z / (alpha - 1) -
        Real.log (riemannZeta ((alpha * s : ℝ) : ℂ)).re / (alpha - 1))
      atTop (nhds 0) := by
    simpa using (hden.const_div_atTop (Real.log Z)).sub (hzeta_log.div_atTop hden)
  have hlimit : Tendsto (fun alpha : ℝ ↦
      Real.log Z + (Real.log Z / (alpha - 1) -
        Real.log (riemannZeta ((alpha * s : ℝ) : ℂ)).re / (alpha - 1)))
      atTop (nhds (Real.log Z)) := by
    simpa using tendsto_const_nhds.add hsmall
  rw [zeta_min_entropy_eq s hs]
  change Tendsto (fun alpha : ℝ ↦ countableRenyiEntropy alpha (zetaDist s hs)) atTop
    (nhds (Real.log Z))
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hscale.eventually_gt_atTop 1] with alpha
      halpha halpha_s
  rw [zeta_renyi_entropy_eq s alpha hs halpha.ne' halpha_s]
  have hzeta_pos : 0 < (riemannZeta ((alpha * s : ℝ) : ℂ)).re :=
    riemannZeta_re_pos_of_one_lt halpha_s
  rw [Real.log_div hzeta_pos.ne' (Real.rpow_pos_of_pos hZ_pos alpha).ne',
    Real.log_rpow hZ_pos]
  have ha1 : alpha - 1 ≠ 0 := sub_ne_zero.mpr halpha.ne'
  have h1a : 1 - alpha ≠ 0 := sub_ne_zero.mpr halpha.ne
  field_simp [ha1, h1a]
  ring

end

end D5.S3.Analytic.Zeta.ZetaMinEntropy
