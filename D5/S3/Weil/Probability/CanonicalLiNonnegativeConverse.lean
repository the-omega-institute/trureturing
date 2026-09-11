/- GID: D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/CanonicalLiNonnegativeConverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegativity of every positive canonical Li coefficient implies standard RH. -/

import D5.S3.Weil.Probability.CanonicalLiGrowthZeroFree
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
A006 reverse only, at the derivative-defined canonical coefficients. The public
premise is nonnegativity at every positive natural index. A007 reverse may consume
this implication; RH-forward positivity and the fixed-lambda1 A013 bound remain open.

Source: Flajolet--Sedgewick, Analytic Combinatorics, Theorem IV.6 and item IV.13,
printed pp.240--242 (Library/notes/flajolet2009analytic.md). The private proof uses
an independent analytic continuation at the positive radius, scalar coefficient
uniqueness, and nonnegative double summation. The finite-subset expansion
map_add_univ supplies the indexed binomial identity; no inconsistent printed
exponent from p.242 is used. The canonical Li specialization is repository assembly.

Proof shape: content; admission_basis=escape-witness (pending independent review).
After inlining, continuation gives the recentered series radius beyond 2h at R-h;
positive_recenter_summable yields original summability at R+h. Its radius inequality
contradicts radius=R. This contradiction supplies radius>=1, hence the exact input
of canonical_li_disk_summability_implies_rh. Utility none: no finite instances,
numerical certificates, arithmetic approximations, or assumed zero-sum formula.

Reuse intake is repo-prior-exposed: six earlier design conclusions are advisory,
not independent verification. Pinned Mathlib db584cd6 supplies recentering,
uniqueness, scalar series and nonnegative Tonelli. The inspected PGF PR43229
assumes bounded finite-measure coefficients and does not supply this boundary
obstruction. Recorded CSLib/Zulip/third-party searches are bounded observations,
not semantic absence. No exact applicable positive-boundary theorem was identified
in those inspected sources. The eligible real-segment uniqueness route uses the
frozen analytic_continuation_unique theorem and discharges the generator equality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter Set FormalMultilinearSeries
open D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
open D5.S3.Zeros.CompletedZeta
open D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
open scoped Topology BigOperators NNReal ENNReal

namespace D5.S3.Weil.Probability.CanonicalLiNonnegativeConverse

private theorem scalar_term_real (a : ℕ → ℝ) (n : ℕ) (v : Fin n → ℝ) :
    FormalMultilinearSeries.ofScalars ℂ (fun k => (a k : ℂ)) n (fun i => (v i : ℂ)) =
      ((a n * ∏ i, v i : ℝ) : ℂ) := by
  simp [FormalMultilinearSeries.ofScalars, List.prod_ofFn]

private theorem positive_recenter_summable (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (x y : ℝ≥0)
    (hx : (x : ℝ≥0∞) < (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius)
    (hy : (y : ℝ≥0∞) < ((FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).changeOrigin (x : ℂ)).radius) :
    Summable (fun n => a n * ((x + y : ℝ≥0) : ℝ) ^ n) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  have hxx : (x : ℂ) ∈ Metric.eball 0 p.radius := by
    simpa [mem_eball_zero_iff, enorm, Complex.nnnorm_real, p] using hx
  have hyy : (y : ℂ) ∈ Metric.eball 0 (p.changeOrigin (x : ℂ)).radius := by
    simpa [mem_eball_zero_iff, enorm, Complex.nnnorm_real, p] using hy
  let f : (Σ k l : ℕ, {s : Finset (Fin (k + l)) // s.card = l}) → ℂ := fun s =>
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => (x : ℂ)) (fun _ => (y : ℂ))
  have freal (s) : f s = ((f s).re : ℂ) ∧ 0 ≤ (f s).re := by
    rcases s with ⟨k, l, s, hs⟩
    dsimp [f]
    rw [changeOriginSeriesTerm_apply]
    have heq : s.piecewise (fun _ => (x : ℂ)) (fun _ => (y : ℂ)) =
        fun i => ((if i ∈ s then (x : ℝ) else (y : ℝ)) : ℂ) := by
      funext i
      simp only [Finset.piecewise]
    rw [heq]
    change (ofScalars ℂ (fun n => (a n : ℂ)) (k + l) _) = _ ∧ _
    simp_rw [← apply_ite Complex.ofReal]
    rw [scalar_term_real]
    simp only [ofReal_re, true_and]
    exact mul_nonneg (ha _) (Finset.prod_nonneg (fun i _ => by split_ifs <;> positivity))
  have hrow (k : ℕ) : HasSum (fun s => f ⟨k, s⟩)
      (p.changeOrigin (x : ℂ) k (fun _ => (y : ℂ))) := by
    apply ContinuousMultilinearMap.hasSum_eval
    have h := (p.hasFPowerSeriesOnBall_changeOrigin k hx.pos).hasSum hxx
    rw [zero_add] at h
    refine HasSum.sigma_of_hasSum h (fun l => ?_) ?_
    · simp only [changeOriginSeries, sum_apply]
      apply hasSum_fintype
    · refine .of_nnnorm_bounded (p.changeOriginSeries_summable_aux₂ hx k) fun s => ?_
      refine (ContinuousMultilinearMap.le_opNNNorm _ _).trans_eq ?_
      simp
  have hsum : Summable (fun s => (f s).re) := by
    apply (summable_sigma_of_nonneg (fun s => (freal s).2)).2
    refine ⟨fun k => (Complex.hasSum_re (hrow k)).summable, ?_⟩
    have h := Complex.hasSum_re ((p.changeOrigin (x : ℂ)).hasSum hyy)
    convert h.summable using 1
    funext k
    exact (Complex.hasSum_re (hrow k)).tsum_eq
  have hsf : Summable f := by
    have h := Complex.summable_ofReal.mpr hsum
    exact h.congr (fun s => (freal s).1.symm)
  have hgroup := (changeOriginIndexEquiv.symm.summable_iff.mpr hsf).sigma
  have hterms : (fun n => ∑' t : Finset (Fin n), f (changeOriginIndexEquiv.symm ⟨n, t⟩)) =
      fun n => ((a n * ((x + y : ℝ≥0) : ℝ) ^ n : ℝ) : ℂ) := by
    funext n
    simp only [tsum_fintype]
    dsimp only [f]
    simp_rw [changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
    rw [← (p n).map_add_univ]
    simp [p, mul_comm]
  simp only [Function.comp_apply] at hgroup
  rw [hterms] at hgroup
  exact Complex.summable_ofReal.mp hgroup


private theorem analytic_germ_eq_of_real_interval (f g : ℂ → ℂ) (x ε : ℝ)
    (hε : 0 < ε) (hf : AnalyticAt ℂ f (x : ℂ)) (hg : AnalyticAt ℂ g (x : ℂ))
    (heq : ∀ t : ℝ, x < t → t < x + ε → f (t : ℂ) = g (t : ℂ)) :
    f =ᶠ[𝓝 (x : ℂ)] g := by
  rcases hf.eventually_eq_or_eventually_ne hg with h | h
  · exact h
  · obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp h
    obtain ⟨t, ht0, ht⟩ := exists_between (lt_min hε hδ)
    have hmem : ((x + t : ℝ) : ℂ) ∈ Metric.ball (x : ℂ) δ ∩ { (x : ℂ) }ᶜ := by
      constructor
      · simpa [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
          Complex.norm_real, abs_of_pos ht0] using ht.trans_le (min_le_right _ _)
      · simpa using (ne_of_gt (show x < x + t by linarith))
    exact False.elim (hball hmem (heq (x + t) (by linarith) (by linarith [min_le_left ε δ])))


private theorem nonnegative_series_positive_boundary_obstruction (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (R : ℝ≥0) (hR : 0 < R)
    (hrad : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius = (R : ℝ≥0∞))
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g (R : ℂ))
    (heq : ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, (R : ℝ) - ε < x → x < R → 0 ≤ x →
      g (x : ℂ) = ∑' n, (a n : ℂ) * (x : ℂ) ^ n) : False := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  obtain ⟨ε, hε, heq⟩ := heq
  obtain ⟨q, r, hq⟩ := hg
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hq.r_pos
  simp only [zero_add] at hδ
  obtain ⟨h, hh0, hh⟩ := exists_between
    (show (0 : ℝ) < min (R : ℝ) (min ε ((δ : ℝ) / 4)) by positivity)
  have hhR : h < R := hh.trans_le (min_le_left _ _)
  have hhε : h < ε := hh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhδ : 4 * h < δ := by
    have := hh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  let d : ℝ≥0 := ⟨h, hh0.le⟩
  let x : ℝ≥0 := ⟨R - h, sub_nonneg.mpr hhR.le⟩
  let y : ℝ≥0 := ⟨2 * h, by positivity⟩
  have hnorm : ‖(-(h : ℂ))‖₊ = d := by
    apply Subtype.ext
    change ‖(-(h : ℂ))‖ = h
    simpa using Complex.norm_of_nonneg hh0.le
  have hdδ : (d : ℝ≥0∞) < δ := by
    exact_mod_cast (show d < δ by change h < (δ : ℝ); linarith)
  have hqx := (hq.mono (ENNReal.coe_pos.mpr hδ0) hδ.le).changeOrigin
    (y := -(h : ℂ)) (by simpa only [hnorm] using hdδ)
  have hcenter : (R : ℂ) + -(h : ℂ) = (x : ℂ) := by
    change (R : ℂ) + -(h : ℂ) = (((R : ℝ) - h : ℝ) : ℂ)
    push_cast
    ring
  rw [hcenter, hnorm] at hqx
  have hxp : (x : ℝ≥0∞) < p.radius := by
    rw [hrad]
    exact_mod_cast (show x < R by change (R : ℝ) - h < R; linarith)
  have hxnorm : ‖(x : ℂ)‖₊ = x := by
    simp [Complex.nnnorm_real]
  have hpx := (p.hasFPowerSeriesOnBall hxp.pos).changeOrigin
    (y := (x : ℂ)) (by simpa only [hxnorm] using hxp)
  rw [zero_add] at hpx
  have hevent : p.sum =ᶠ[𝓝 (x : ℂ)] g := by
    apply analytic_germ_eq_of_real_interval p.sum g (x : ℝ) (h / 2)
      (by positivity) hpx.analyticAt hqx.analyticAt
    intro t hxt ht
    have he := heq t (by change (R : ℝ) - h < t at hxt; linarith)
      (by change t < (R : ℝ) - h + h / 2 at ht; linarith) (le_trans x.coe_nonneg hxt.le)
    simpa [p, FormalMultilinearSeries.sum, ofScalars_apply_eq, smul_eq_mul, mul_comm] using he.symm
  have heqseries := hpx.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    hqx.hasFPowerSeriesAt hevent
  have hyr : (y : ℝ≥0∞) < (p.changeOrigin (x : ℂ)).radius := by
    rw [heqseries]
    apply lt_of_lt_of_le _ hqx.r_le
    rw [lt_tsub_iff_right]
    exact_mod_cast (show y + d < δ by change 2 * h + h < (δ : ℝ); linarith)
  have hs := positive_recenter_summable a ha x y hxp hyr
  have hle : ((x + y : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    simpa [p, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha _)] using hs
  rw [hrad] at hle
  have hle' : x + y ≤ R := ENNReal.coe_le_coe.mp hle
  have : (R : ℝ) - h + 2 * h ≤ R := by exact_mod_cast hle'
  linarith


private theorem li_generator_analytic_on_nonnegative_real_segment (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < 1) : AnalyticAt ℂ liGenerator (x : ℂ) := by
  have hsub : (1 : ℂ) - (x : ℂ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hx1.ne')
  have hs : 1 ≤ (1 - x)⁻¹ := by
    exact (one_le_inv₀ (by linarith : (0 : ℝ) < 1 - x)).mpr (by linarith)
  have hn : xiReading ((1 - (x : ℂ))⁻¹) ≠ 0 := by
    intro h
    have ht := ((xiReading_eq_zero_iff_nontrivial _).mp h).2.2
    have hre : ((1 - (x : ℂ))⁻¹).re = (1 - x)⁻¹ := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [hre] at ht
    linarith
  have hxi := xi_reading_differentiable.analyticAt ((1 - (x : ℂ))⁻¹)
  have hlog : AnalyticAt ℂ (logDeriv xiReading) ((1 - (x : ℂ))⁻¹) :=
    hxi.deriv.div hxi hn
  have hp : AnalyticAt ℂ (fun z : ℂ => (1 - z)⁻¹) (x : ℂ) :=
    (analyticAt_const.sub analyticAt_id).inv hsub
  exact (hp.pow 2).mul (hlog.comp (f := fun z : ℂ => (1 - z)⁻¹) hp)

private theorem canonical_li_nonnegative_summable
    (nonnegative : ∀ n : ℕ, 1 ≤ n → 0 ≤ canonicalLiCoefficient n)
    (r : ℝ≥0) (hr : r < 1) :
    Summable (fun n : ℕ => |canonicalLiCoefficient (n + 1)| * (r : ℝ) ^ n) := by
  let p := FormalMultilinearSeries.ofScalars ℂ
    (fun n => (canonicalLiCoefficient (n + 1) : ℂ))
  have ha (n : ℕ) : 0 ≤ canonicalLiCoefficient (n + 1) := nonnegative _ (by omega)
  have hlocal : ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => (canonicalLiCoefficient (n + 1) : ℂ) * z ^ n) (liGenerator z) := by
    simpa only [liGenerator, one_div, zpow_neg, zpow_ofNat, inv_pow] using canonical_li_local_expansion
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp hlocal
  let t : ℝ≥0 := ⟨δ / 2, by positivity⟩
  have ht0 : 0 < t := by change 0 < δ / 2; positivity
  have htmem : (t : ℂ) ∈ Metric.ball 0 δ := by
    simpa [Metric.mem_ball, dist_zero_right, Complex.norm_real, abs_of_nonneg t.coe_nonneg]
      using (show (t : ℝ) < δ by change δ / 2 < δ; linarith)
  have htSum : Summable (fun n => canonicalLiCoefficient (n + 1) * (t : ℝ)^n) := by
    apply Complex.summable_ofReal.mp
    simpa using (hδ htmem).summable
  have htRadius : (t : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    simpa [p, ofScalars_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha _)] using htSum
  have hp0 : 0 < p.radius := (ENNReal.coe_pos.mpr ht0).trans_le htRadius
  have hone : 1 ≤ p.radius := by
    by_contra h
    have hlt : p.radius < 1 := lt_of_not_ge h
    have htop : p.radius ≠ ⊤ := ne_top_of_lt hlt
    let R := p.radius.toNNReal
    have hR : p.radius = (R : ℝ≥0∞) := (ENNReal.coe_toNNReal htop).symm
    have hR0 : 0 < R := ENNReal.coe_pos.mp (hR ▸ hp0)
    have hR1 : R < 1 := by exact_mod_cast (show (R : ℝ≥0∞) < 1 from hR ▸ hlt)
    apply nonnegative_series_positive_boundary_obstruction
      (fun n => canonicalLiCoefficient (n + 1)) ha R hR0 hR liGenerator
      (li_generator_analytic_on_nonnegative_real_segment R R.coe_nonneg (by exact_mod_cast hR1))
    let U : Set ℂ := Complex.ofReal '' Ico (0 : ℝ) R
    have hPa : AnalyticOnNhd ℂ p.sum U := by
      rintro z ⟨x, hx, rfl⟩
      apply p.analyticOnNhd
      simp only [mem_eball_zero_iff]
      rw [hR]
      have : ‖(x : ℂ)‖₊ = ⟨x, hx.1⟩ := by
        apply Subtype.ext
        exact Complex.norm_of_nonneg hx.1
      simpa [enorm, this] using (ENNReal.coe_lt_coe.mpr (show (⟨x, hx.1⟩ : ℝ≥0) < R from hx.2))
    have hGa : AnalyticOnNhd ℂ liGenerator U := by
      rintro z ⟨x, hx, rfl⟩
      exact li_generator_analytic_on_nonnegative_real_segment x hx.1
        (hx.2.trans (by exact_mod_cast hR1))
    have hevent : p.sum =ᶠ[𝓝 (0 : ℂ)] liGenerator := by
      filter_upwards [hlocal] with z hz
      simpa [p, FormalMultilinearSeries.sum, ofScalars_apply_eq, smul_eq_mul, mul_comm] using hz.tsum_eq
    have heq := analytic_continuation_unique hPa hGa
      (isPreconnected_Ico.image _ Complex.continuous_ofReal.continuousOn)
      (show (0 : ℂ) ∈ U from ⟨0, ⟨le_rfl, by exact_mod_cast hR0⟩, by simp⟩) hevent
    refine ⟨R, by exact_mod_cast hR0, ?_⟩
    intro x _ hx hx0
    have he := heq (show (x : ℂ) ∈ U from ⟨x, ⟨hx0, hx⟩, rfl⟩)
    simpa [p, FormalMultilinearSeries.sum, ofScalars_apply_eq, smul_eq_mul, mul_comm] using he.symm
  have hs := p.summable_norm_mul_pow ((ENNReal.coe_lt_one_iff.mpr hr).trans_le hone)
  simpa [p, ofScalars_norm, Complex.norm_real, Real.norm_eq_abs] using hs


/-- Nonnegativity at every positive index of the canonical Li sequence implies RH. -/
theorem canonical_li_nonnegative_implies_rh
    (nonnegative : ∀ n : ℕ, 1 ≤ n → 0 ≤ canonicalLiCoefficient n) :
    RiemannHypothesis := by
  exact D5.S3.Weil.Probability.CanonicalLiGrowthZeroFree.canonical_li_disk_summability_implies_rh
    (canonical_li_nonnegative_summable nonnegative)

#print axioms canonical_li_nonnegative_implies_rh

end D5.S3.Weil.Probability.CanonicalLiNonnegativeConverse
