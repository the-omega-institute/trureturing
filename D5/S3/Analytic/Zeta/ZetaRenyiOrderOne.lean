/- GID: D5/S3/Analytic/Zeta/ZetaRenyiOrderOne
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The order-one endpoint of the zeta law's Renyi entropy family. -/

import D5.S3.Analytic.Zeta.ZetaRenyiEntropy

/- Provenance: Native proof over pinned mathlib. -/

/- Search and proof receipt (2026-08-23).

   * The repository was searched for `Renyi`, `order one`, `expectedLog`, zeta derivatives, and
     logarithmic derivatives. `D5/S3/RenyiDivergence/OrderOneLimit.lean` supplied the punctured
     slope pattern; `ZetaEntropy.lean` supplied `zeta_entropy_eq`; and
     `ZetaRenyiEntropy.lean` supplied the closed form. No existing zeta-Renyi order-one endpoint
     was found.
   * Pinned mathlib was searched for `riemannZeta` differentiability/derivatives,
     `LSeries` derivatives, logarithmic derivatives, derivatives of `tsum`, real parts of complex
     derivatives, and slope limits. The relevant hits were `LSeries_hasDerivAt` and
     `LSeriesSummable_logMul_of_lt_re` in `NumberTheory/LSeries/Deriv.lean`,
     `LSeries.abscissaOfAbsConv_one` and `LSeries_one_eq_riemannZeta` in
     `NumberTheory/LSeries/Dirichlet.lean`, `HasDerivAt.real_of_complex` in
     `Analysis/Complex/RealDeriv.lean`, `Real.HasDerivAt.log` in
     `Analysis/SpecialFunctions/Log/Deriv.lean`, and `hasDerivAt_iff_tendsto_slope` in
     `Analysis/Calculus/Deriv/Slope.lean`. The generic `hasDerivAt_tsum` API was found in
     `Analysis/Calculus/SmoothSeries.lean` but was not needed because the L-series API already
     packages the justified derivative and its logarithm-weighted series.
   * The derivative identity obtained from those declarations is
     `re (zeta'(s)) = -sum_n log(n) n^(-s)`. After normalization this identifies
     `expectedLog (zetaDist s hs)` with `-re (zeta'(s)) / re (zeta(s))`, connecting the
     derivative of the closed-form numerator to the imported Shannon entropy formula.
   * The final limit uses `nhdsWithin 1 {1}^c`, not `nhds 1`: totalized division makes
     `countableRenyiEntropy 1 p = 0`. No one-sided or bounded restriction is needed; continuity
     of `alpha * s` makes `1 < alpha * s` eventual in the full two-sided neighborhood.
   * A temporary `#print axioms` probe reported exactly
     `[propext, Classical.choice, Quot.sound]` for `zeta_renyi_entropy_tendsto_entropy`; the probe
     was then deleted. -/

namespace D5.S3.Analytic.Zeta.ZetaRenyiOrderOne

open Filter
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.ZetaRenyiEntropy

noncomputable section

private lemma riemannZeta_deriv_re_eq_neg_tsum_log_weight (s : ℝ) (hs : 1 < s) :
    (deriv riemannZeta (s : ℂ)).re =
      -(∑' n : ℕ, Real.log n * (n : ℝ) ^ (-s)) := by
  have habscissa : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < ((s : ℂ)).re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hs
  have hL := LSeries_hasDerivAt (f := (1 : ℕ → ℂ)) habscissa
  have heq : (fun z : ℂ ↦ riemannZeta z) =ᶠ[nhds (s : ℂ)] LSeries (1 : ℕ → ℂ) := by
    filter_upwards [
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hs)] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  have hzeta : HasDerivAt riemannZeta
      (-LSeries (LSeries.logMul (1 : ℕ → ℂ)) (s : ℂ)) (s : ℂ) :=
    hL.congr_of_eventuallyEq heq
  rw [hzeta.deriv]
  have hsum : LSeriesSummable (LSeries.logMul (1 : ℕ → ℂ)) (s : ℂ) :=
    LSeriesSummable_logMul_of_lt_re habscissa
  rw [LSeries, Complex.neg_re, Complex.re_tsum hsum]
  congr 1
  apply tsum_congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hn0 : n ≠ 0 := hn.ne'
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn0]
    simp only [LSeries.logMul, Pi.one_apply, mul_one]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnR.le,
      ← Complex.ofReal_cpow n.cast_nonneg, ← Complex.ofReal_div]
    rw [Complex.ofReal_re, div_eq_mul_inv, ← Real.rpow_neg hnR.le]

private lemma expectedLog_eq_neg_zeta_logDeriv (s : ℝ) (hs : 1 < s) :
    expectedLog (zetaDist s hs) =
      -(deriv riemannZeta (s : ℂ)).re / (riemannZeta (s : ℂ)).re := by
  have hsum := summable_log_weight s hs
  rw [expectedLog]
  rw [show (fun n : ℕ ↦ pmfReal (zetaDist s hs) n * Real.log n) =
      fun n : ℕ ↦ (partitionFunction s).toReal⁻¹ *
        (Real.log n * (n : ℝ) ^ (-s)) by
    funext n
    rw [zeta_real_apply]
    ring]
  rw [hsum.tsum_mul_left, riemannZeta_deriv_re_eq_neg_tsum_log_weight s hs,
    partition_toReal_eq_zeta_re s hs]
  have hZ : (riemannZeta (s : ℂ)).re ≠ 0 :=
    (riemannZeta_re_pos_of_one_lt hs).ne'
  field_simp

private lemma hasDerivAt_renyi_numerator (s : ℝ) (hs : 1 < s) :
    HasDerivAt
      (fun alpha : ℝ ↦
        Real.log (riemannZeta ((alpha * s : ℝ) : ℂ)).re -
          alpha * Real.log (riemannZeta (s : ℂ)).re)
      (-countableEntropy (zetaDist s hs)) 1 := by
  have hs_ne_one : (s : ℂ) ≠ 1 := by
    exact_mod_cast hs.ne'
  have hzeta_complex := (differentiableAt_riemannZeta hs_ne_one).hasDerivAt
  have hzeta_real : HasDerivAt (fun x : ℝ ↦ (riemannZeta (x : ℂ)).re)
      (deriv riemannZeta (s : ℂ)).re s := hzeta_complex.real_of_complex
  have hscale : HasDerivAt (fun alpha : ℝ ↦ alpha * s) s 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const s
  have hcomp : HasDerivAt
      (fun alpha : ℝ ↦ (riemannZeta ((alpha * s : ℝ) : ℂ)).re)
      ((deriv riemannZeta (s : ℂ)).re * s) 1 := by
    have hzeta_real' : HasDerivAt (fun x : ℝ ↦ (riemannZeta (x : ℂ)).re)
        (deriv riemannZeta (s : ℂ)).re (1 * s) := by
      simpa using hzeta_real
    have hraw := hzeta_real'.comp 1 hscale
    have hfun :
        ((fun x : ℝ ↦ (riemannZeta (x : ℂ)).re) ∘ fun alpha : ℝ ↦ alpha * s) =
          (fun alpha : ℝ ↦ (riemannZeta ((alpha * s : ℝ) : ℂ)).re) := by
      funext alpha
      simp
    rw [← hfun]
    exact hraw
  have hZ : (riemannZeta (s : ℂ)).re ≠ 0 :=
    (riemannZeta_re_pos_of_one_lt hs).ne'
  have hlog : HasDerivAt
      (fun alpha : ℝ ↦ Real.log (riemannZeta ((alpha * s : ℝ) : ℂ)).re)
      ((deriv riemannZeta (s : ℂ)).re * s / (riemannZeta (s : ℂ)).re) 1 := by
    simpa using hcomp.log (by simpa using hZ)
  have hlinear : HasDerivAt
      (fun alpha : ℝ ↦ alpha * Real.log (riemannZeta (s : ℂ)).re)
      (Real.log (riemannZeta (s : ℂ)).re) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const
      (Real.log (riemannZeta (s : ℂ)).re)
  apply (hlog.sub hlinear).congr_deriv
  rw [zeta_entropy_eq s hs, expectedLog_eq_neg_zeta_logDeriv s hs,
    partition_toReal_eq_zeta_re s hs]
  field_simp [hZ]
  ring

/-- The Renyi entropies of the zeta law converge to Shannon entropy as the order tends to one.

The filter is punctured because `countableRenyiEntropy 1 p = 0` under Lean's totalized division,
whereas the order-one endpoint is the limit and is generally nonzero. No one-sided restriction is
needed: `1 < alpha * s` holds throughout a sufficiently small two-sided neighborhood of one. -/
theorem zeta_renyi_entropy_tendsto_entropy (s : ℝ) (hs : 1 < s) :
    Tendsto (fun alpha : ℝ ↦ countableRenyiEntropy alpha (zetaDist s hs))
      (nhdsWithin 1 {(1 : ℝ)}ᶜ) (nhds (countableEntropy (zetaDist s hs))) := by
  let numerator : ℝ → ℝ := fun alpha ↦
    Real.log (riemannZeta ((alpha * s : ℝ) : ℂ)).re -
      alpha * Real.log (riemannZeta (s : ℂ)).re
  have hnum : HasDerivAt numerator (-countableEntropy (zetaDist s hs)) 1 :=
    hasDerivAt_renyi_numerator s hs
  have hslope : Tendsto (slope numerator 1) (nhdsWithin 1 {(1 : ℝ)}ᶜ)
      (nhds (-countableEntropy (zetaDist s hs))) :=
    hasDerivAt_iff_tendsto_slope.mp hnum
  have hneg : Tendsto (fun alpha ↦ -slope numerator 1 alpha)
      (nhdsWithin 1 {(1 : ℝ)}ᶜ) (nhds (countableEntropy (zetaDist s hs))) := by
    simpa using hslope.neg
  refine hneg.congr' ?_
  have hmul : ContinuousAt (fun alpha : ℝ ↦ alpha * s) 1 :=
    continuousAt_id.mul continuousAt_const
  have heventually_s : ∀ᶠ alpha in nhds 1, 1 < alpha * s :=
    hmul.eventually (isOpen_Ioi.mem_nhds (by simpa using hs))
  filter_upwards [self_mem_nhdsWithin, heventually_s.filter_mono inf_le_left] with alpha
      halpha halpha_s
  have halpha_ne : alpha ≠ 1 := by simpa using halpha
  rw [zeta_renyi_entropy_eq s alpha hs halpha_ne halpha_s]
  have hZ : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
  have hZa : 0 < (riemannZeta ((alpha * s : ℝ) : ℂ)).re :=
    riemannZeta_re_pos_of_one_lt halpha_s
  rw [Real.log_div hZa.ne' (Real.rpow_pos_of_pos hZ alpha).ne', Real.log_rpow hZ,
    slope_def_field]
  dsimp [numerator]
  simp only [one_mul, sub_self]
  field_simp [halpha_ne, halpha_ne.symm]
  ring

end

end D5.S3.Analytic.Zeta.ZetaRenyiOrderOne
