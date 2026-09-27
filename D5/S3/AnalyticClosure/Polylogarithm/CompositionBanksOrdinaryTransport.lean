/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionBanksOrdinaryTransport
   generality: G
   mirror-B: none(waiver:private-implementation-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Private ordinary full-slit transport for the actual positive-composition branch. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionBoundary
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingTransport
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction
import D5.S3.AnalyticClosure.Polylogarithm.CompositionSlit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksOrdinaryTransport

open D5.S3.AnalyticClosure.Polylogarithm
open CompositionBoundary CompositionContinuation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open private radial_one_sub_bound radial_majorant_integrable
  radial_one_sub_uniform_bound inner_arc_decay from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
open private admissibleRemainder from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction

private theorem ordinary_angular_subarc_vanishes : ∀ (first : ℕ+) (suffix : List ℕ+)
    (hfirst : 1 < (first : ℕ)) (ρ D : ℝ) (N : ℕ),
    0 < ρ → 0 ≤ D →
    (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
          (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - w)‖ ≤
        D * (1 + ‖-Complex.log w‖) ^ N) →
    ∀ (r a b : ℝ), 0 < r → r < ρ →
      -Real.pi < a → b < Real.pi → a ≤ b →
      Tendsto
        (fun eps : ℝ ↦ ∫ θ in a..b,
          (-I) * (((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) *
            CompositionContinuation.continued
              (⟨(first : ℕ) - 1, by omega⟩ :: suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) /
              (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)))
        (𝓝[>] 0) (𝓝 0) := by
  intro first suffix hfirst ρ D N hρ hD hbound r a b hr hrρ ha hb hab
  have hdecay := inner_arc_decay (Real.pi + |Real.log r|) 1 N
    (by positivity) (by omega)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmajor : Tendsto
      (fun eps : ℝ ↦ (2 * D * r * |b - a|) *
        (eps ^ 1 * (1 + (Real.pi + |Real.log r|) + |Real.log eps|) ^ N))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hdecay.const_mul (2 * D * r * |b - a|)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsGT (show 0 < min 1 (1 / (2 * r)) by positivity)]
      with eps heps
    have heps1 : eps < 1 := heps.2.trans_le (min_le_left _ _)
    have hprod : 0 < eps * r := mul_pos heps.1 hr
    have hprodρ : eps * r < ρ :=
      (mul_lt_of_lt_one_left hr heps1).trans hrρ
    have hprodHalf : eps * r < 1 / 2 := by
      have hepsHalf : eps < 1 / (2 * r) := heps.2.trans_le (min_le_right _ _)
      calc
        eps * r < (1 / (2 * r)) * r := mul_lt_mul_of_pos_right hepsHalf hr
        _ = 1 / 2 := by field_simp
    have hpoint : ∀ θ ∈ Set.uIcc a b,
        ‖(-I) * (((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) *
            CompositionContinuation.continued
              (⟨(first : ℕ) - 1, by omega⟩ :: suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) /
              (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ≤
          2 * D * (eps * r) *
            (1 + Real.pi + |Real.log r| + |Real.log eps|) ^ N := by
      intro θ hθ
      rw [Set.uIcc_of_le hab] at hθ
      have hθneg : -Real.pi < θ := ha.trans_le hθ.1
      have hθpos : θ < Real.pi := hθ.2.trans_lt hb
      let w : ℂ := ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)
      have hwslit : w ∈ Complex.slitPlane := by
        have hexp : Complex.exp ((θ : ℂ) * I) ∈ Complex.slitPlane := by
          rw [Complex.exp_mem_slitPlane]
          have hmod : toIocMod Real.two_pi_pos (-Real.pi) θ = θ := by
            apply (toIocMod_eq_self (hp := Real.two_pi_pos)
              (a := -Real.pi) (b := θ)).2
            exact ⟨hθneg, by linarith [Real.pi_pos]⟩
          simpa [hmod] using hθpos.ne
        rw [Complex.mem_slitPlane_iff] at hexp ⊢
        simp only [w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, Complex.mul_im, add_zero]
        exact hexp.imp (fun h ↦ mul_pos hprod h) (mul_ne_zero hprod.ne')
      have hwnorm : ‖w‖ = eps * r := by
        simp [w, abs_of_pos heps.1, abs_of_pos hr]
      have hw0 : 0 < ‖w‖ := by rw [hwnorm]; exact hprod
      have hwρ : ‖w‖ < ρ := by rw [hwnorm]; exact hprodρ
      have hlogexp : Complex.log (Complex.exp ((θ : ℂ) * I)) = (θ : ℂ) * I := by
        apply Complex.log_exp
        · simpa using hθneg
        · simpa using hθpos.le
      have hlog : Complex.log w = (Real.log (eps * r) : ℂ) + (θ : ℂ) * I := by
        dsimp [w]
        rw [Complex.log_ofReal_mul hprod (Complex.exp_ne_zero _), hlogexp]
      have hlognorm : ‖-Complex.log w‖ ≤
          |Real.log eps| + |Real.log r| + Real.pi := by
        rw [hlog, norm_neg]
        calc
          ‖(Real.log (eps * r) : ℂ) + (θ : ℂ) * I‖ ≤
              ‖(Real.log (eps * r) : ℂ)‖ + ‖(θ : ℂ) * I‖ := norm_add_le _ _
          _ = |Real.log (eps * r)| + |θ| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, norm_I, mul_one]
          _ ≤ (|Real.log eps| + |Real.log r|) + Real.pi := by
            gcongr
            · rw [Real.log_mul heps.1.ne' hr.ne']
              exact abs_add_le _ _
            · exact (abs_le.mpr ⟨hθneg.le, hθpos.le⟩)
      have hden : ‖(1 - w)⁻¹‖ ≤ 2 := by
        have hinv := Complex.norm_one_add_mul_inv_le
          (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
          (by rw [norm_neg, hwnorm]; linarith) (z := -w)
        have hraw : ‖(1 - w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := by
          simpa [sub_eq_add_neg, mul_neg, norm_neg] using hinv
        calc
          ‖(1 - w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := hraw
          _ ≤ 2 := by
            rw [hwnorm]
            have hhalf : (1 / 2 : ℝ) ≤ 1 - eps * r := by
              linarith [hprodHalf]
            have hrecip := one_div_le_one_div_of_le
              (show (0 : ℝ) < 1 / 2 by norm_num) hhalf
            norm_num [one_div] at hrecip
            exact hrecip
      have hprev := hbound w hwslit hw0 hwρ
      change ‖(-I) * w *
          CompositionContinuation.continued
            (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - w) / (1 - w)‖ ≤ _
      rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_neg, norm_I, one_mul]
      calc
        ‖w‖ * ‖CompositionContinuation.continued
            (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - w)‖ * ‖(1 - w)⁻¹‖ ≤
            (eps * r) * (D * (1 + ‖-Complex.log w‖) ^ N) * 2 := by
          rw [hwnorm]
          calc
            (eps * r) * ‖CompositionContinuation.continued
                  (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - w)‖ * ‖(1 - w)⁻¹‖ ≤
                (eps * r) * (D * (1 + ‖-Complex.log w‖) ^ N) * ‖(1 - w)⁻¹‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hprev hprod.le) (norm_nonneg _)
            _ ≤ (eps * r) * (D * (1 + ‖-Complex.log w‖) ^ N) * 2 :=
              mul_le_mul_of_nonneg_left hden
                (mul_nonneg hprod.le (mul_nonneg hD (pow_nonneg (by positivity) _)))
        _ = (2 * D * (eps * r)) * (1 + ‖-Complex.log w‖) ^ N := by ring
        _ ≤ (2 * D * (eps * r)) *
            (1 + Real.pi + |Real.log r| + |Real.log eps|) ^ N := by
          have hpow : (1 + ‖-Complex.log w‖) ^ N ≤
              (1 + Real.pi + |Real.log r| + |Real.log eps|) ^ N :=
            pow_le_pow_left₀ (by positivity) (by linarith [hlognorm]) N
          exact mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (mul_nonneg (by norm_num) hD) hprod.le)
    calc
      ‖∫ θ in a..b,
          (-I) * (((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) *
            CompositionContinuation.continued
              (⟨(first : ℕ) - 1, by omega⟩ :: suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) /
              (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ≤
          (2 * D * (eps * r) *
            (1 + Real.pi + |Real.log r| + |Real.log eps|) ^ N) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro θ hθ
        exact hpoint θ (uIoc_subset_uIcc hθ)
      _ = (2 * D * r * |b - a|) *
          (eps ^ 1 * (1 + (Real.pi + |Real.log r|) + |Real.log eps|) ^ N) := by
        ring
private theorem ordinary_integral_identity : ∀ (first : ℕ+) (suffix : List ℕ+)
    (hfirst : 1 < (first : ℕ)) (ρ D : ℝ) (N : ℕ),
    0 < ρ → ρ < 1 → 0 ≤ D →
    (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
          (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - w)‖ ≤
        D * (1 + ‖-Complex.log w‖) ^ N) →
    ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      (∫ t in (0 : ℝ)..1, w *
          (-CompositionContinuation.continued
              (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - (t : ℂ) * w) /
            (1 - (t : ℂ) * w))) =
        CompositionContinuation.continued (first :: suffix) (1 - w) -
          (CompositionBoundary.zeta first suffix : ℂ) := by
  intro first suffix hfirst ρ D N hρ hρ1 hD hbound w hw hw0 hwρ
  have hordinaryDeriv : ∀ (first' : ℕ+) (suffix' : List ℕ+)
      (hfirst' : 1 < (first' : ℕ)) (u : ℂ),
      u ≠ 1 → 1 - u ∈ CompositionContinuation.omega →
      HasDerivAt
        (fun v : ℂ ↦ CompositionContinuation.continued (first' :: suffix') (1 - v))
        (-CompositionContinuation.continued
          (⟨(first' : ℕ) - 1, by omega⟩ :: suffix') (1 - u) / (1 - u)) u := by
    obtain ⟨_, _, _, _, ordinaryDeriv⟩ := CompositionSlit.result
    intro first' suffix' hfirst' u hu hω
    have hzu : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have hz := ordinaryDeriv first' suffix' hfirst' (1 - u) hω
    rw [if_neg hzu] at hz
    have hinner : HasDerivAt (fun v : ℂ ↦ 1 - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (1 : ℂ)
    simpa [Function.comp_def, mul_neg, neg_div] using hz.comp u hinner
  have hpositiveRay : ∀ (first' : ℕ+) (suffix' : List ℕ+),
      1 < (first' : ℕ) → ∀ (s : ℝ), 0 < s →
      Tendsto
        (fun eps : ℝ ↦ CompositionContinuation.continued (first' :: suffix')
          (1 - (eps * s : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 (CompositionBoundary.zeta first' suffix' : ℂ)) := by
    intro first' suffix' hfirst' s hs
    have hreal : Tendsto (fun eps : ℝ ↦ 1 - eps * s) (𝓝[>] 0) (𝓝 1) := by
      have hid : Tendsto (fun eps : ℝ ↦ eps) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using tendsto_const_nhds.sub (hid.mul_const s)
    have hto1 : Tendsto (fun eps : ℝ ↦ 1 - eps * s) (𝓝[>] 0) (𝓝[<] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hreal, ?_⟩
      filter_upwards [eventually_mem_nhdsWithin] with eps heps
      exact sub_lt_self 1 (mul_pos heps hs)
    have hnormalized :=
      (CompositionBoundary.result first' suffix' hfirst').2.2.2.2.2.comp hto1
    have hpower : Tendsto
        (fun eps : ℝ ↦ (((1 - eps * s : ℝ) : ℂ) ^ CompositionDisk.depth suffix'))
        (𝓝[>] 0) (𝓝 1) := by
      have hto1' : Tendsto (fun eps : ℝ ↦ ((1 - eps * s : ℝ) : ℂ))
          (𝓝[>] 0) (𝓝 (1 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).comp hreal
      simpa using hto1'.pow (CompositionDisk.depth suffix')
    have hproduct : Tendsto
        (fun eps : ℝ ↦ CompositionDisk.normalized first' suffix'
            ((1 - eps * s : ℝ) : ℂ) *
          (((1 - eps * s : ℝ) : ℂ) ^ CompositionDisk.depth suffix'))
        (𝓝[>] 0) (𝓝 (CompositionBoundary.zeta first' suffix' : ℂ)) := by
      simpa using hnormalized.mul hpower
    refine hproduct.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin,
      (tendsto_order.1 hreal).1 0 zero_lt_one] with eps heps hpos
    have hz0 : (1 - eps * s : ℝ) ≠ 0 := ne_of_gt hpos
    have hupp : 1 - eps * s < 1 := sub_lt_self 1 (mul_pos heps hs)
    have hnorm : ‖((1 - eps * s : ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      exact hupp
    have hsource := ((CompositionSlit.result).2.1 (first' :: suffix')).2
      ((1 - eps * s : ℝ) : ℂ) hnorm
    have hnormalizedSource :=
      (CompositionBoundary.result first' suffix' hfirst').2.2.2.2.1
        ((1 - eps * s : ℝ) : ℂ) hnorm (ofReal_ne_zero.mpr hz0)
    have hzcast : ((1 - eps * s : ℝ) : ℂ) = 1 - ((eps * s : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [← hzcast, hsource, hnormalizedSource]
    exact div_mul_cancel₀ _ (pow_ne_zero _ (ofReal_ne_zero.mpr hz0))
  have hangularFTC : ∀ (first' : ℕ+) (suffix' : List ℕ+)
      (hfirst' : 1 < (first' : ℕ)) (eps a b : ℝ),
      0 < eps → eps < 1 → -Real.pi < a → b < Real.pi → a ≤ b →
        ∫ θ in a..b,
            (-I) * ((eps : ℂ) * Complex.exp ((θ : ℂ) * I)) *
              CompositionContinuation.continued
                (⟨(first' : ℕ) - 1, by omega⟩ :: suffix')
                  (1 - (eps : ℂ) * Complex.exp ((θ : ℂ) * I)) /
                (1 - (eps : ℂ) * Complex.exp ((θ : ℂ) * I)) =
          CompositionContinuation.continued (first' :: suffix')
              (1 - (eps : ℂ) * Complex.exp ((b : ℂ) * I)) -
            CompositionContinuation.continued (first' :: suffix')
              (1 - (eps : ℂ) * Complex.exp ((a : ℂ) * I)) := by
    intro first' suffix' hfirst' eps a b heps heps1 ha hb hab
    let F : ℂ → ℂ := fun u ↦
      CompositionContinuation.continued (first' :: suffix') (1 - u)
    let circle : ℝ → ℂ := fun θ ↦ (eps : ℂ) * Complex.exp ((θ : ℂ) * I)
    have hcircle : ∀ θ ∈ Set.Icc a b, circle θ ∈ Complex.slitPlane := by
      intro θ hθ
      have hexp : Complex.exp ((θ : ℂ) * I) ∈ Complex.slitPlane := by
        rw [Complex.exp_mem_slitPlane]
        have hmod : toIocMod Real.two_pi_pos (-Real.pi) θ = θ := by
          apply (toIocMod_eq_self (hp := Real.two_pi_pos)
            (a := -Real.pi) (b := θ)).2
          exact ⟨ha.trans_le hθ.1,
            by linarith [hθ.2.trans_lt hb, Real.pi_pos]⟩
        simpa [hmod] using (hθ.2.trans_lt hb).ne
      rw [Complex.mem_slitPlane_iff] at hexp ⊢
      simp only [circle, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.mul_im, add_zero]
      exact hexp.imp (fun h ↦ mul_pos heps h) (mul_ne_zero heps.ne')
    have hcircleNorm : ∀ θ : ℝ, ‖circle θ‖ = eps := by
      intro θ
      simp [circle, abs_of_pos heps]
    have hderiv : ∀ θ ∈ Set.uIcc a b,
        HasDerivAt (fun x : ℝ ↦ F (circle x))
          ((-I) * circle θ *
            CompositionContinuation.continued
              (⟨(first' : ℕ) - 1, by omega⟩ :: suffix') (1 - circle θ) /
                (1 - circle θ)) θ := by
      intro θ hθ
      rw [Set.uIcc_of_le hab] at hθ
      have hslit := hcircle θ hθ
      have hcircleOne : circle θ ≠ 1 := by
        intro hone
        have : ‖circle θ‖ = 1 := by rw [hone, norm_one]
        linarith [hcircleNorm θ]
      have hcomplexCircle : HasDerivAt
          (fun x : ℂ ↦ (eps : ℂ) * Complex.exp (x * I))
          (circle θ * I) (θ : ℂ) := by
        simpa [circle, mul_assoc] using
          (((hasDerivAt_id (θ : ℂ)).mul_const I).cexp.const_mul (eps : ℂ))
      have hcomp := (hordinaryDeriv first' suffix' hfirst' (circle θ) hcircleOne
        (by simpa [CompositionContinuation.omega] using hslit)).comp
          (θ : ℂ) hcomplexCircle
      have hreal := hcomp.comp_ofReal
      change HasDerivAt (fun x : ℝ ↦ F (circle x)) _ θ at hreal
      convert hreal using 1 <;> ring
    have hint : IntervalIntegrable (fun θ : ℝ ↦
        (-I) * circle θ *
          CompositionContinuation.continued
            (⟨(first' : ℕ) - 1, by omega⟩ :: suffix') (1 - circle θ) /
              (1 - circle θ)) MeasureTheory.volume a b := by
      apply ContinuousOn.intervalIntegrable
      intro θ hθ
      rw [Set.uIcc_of_le hab] at hθ
      have hslit := hcircle θ hθ
      have hω : 1 - circle θ ∈ CompositionContinuation.omega := by
        simpa [CompositionContinuation.omega] using hslit
      have hcircleCont : ContinuousAt circle θ := by fun_prop
      have hinner : ContinuousAt (fun x : ℝ ↦ (1 : ℂ) - circle x) θ := by fun_prop
      have houter : ContinuousAt (fun u : ℂ ↦
          CompositionContinuation.continued
            (⟨(first' : ℕ) - 1, by omega⟩ :: suffix') u) (1 - circle θ) :=
        (((CompositionSlit.result).2.1 _).1 _ hω).continuousAt
      have hnum : ContinuousAt (fun x : ℝ ↦
          CompositionContinuation.continued
            (⟨(first' : ℕ) - 1, by omega⟩ :: suffix') (1 - circle x)) θ :=
        ContinuousAt.comp
          (g := fun u : ℂ ↦ CompositionContinuation.continued
            (⟨(first' : ℕ) - 1, by omega⟩ :: suffix') u)
          (f := fun x : ℝ ↦ (1 : ℂ) - circle x) houter hinner
      have hden : (1 : ℂ) - circle θ ≠ 0 := by
        intro hzero
        have hone : circle θ = 1 := (sub_eq_zero.mp hzero).symm
        have : ‖circle θ‖ = 1 := by rw [hone, norm_one]
        linarith [hcircleNorm θ]
      exact (((continuousAt_const.mul hcircleCont).mul hnum).div hinner hden).continuousWithinAt
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simpa [F, circle] using hftc
  let r : ℝ := ρ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrρ : r < ρ := by dsimp [r]; linarith
  have hr1 : r < 1 := hrρ.trans hρ1
  have hargneg : -Real.pi < Complex.arg w := Complex.neg_pi_lt_arg w
  have hargpos : Complex.arg w < Real.pi := by
    rw [Complex.arg_lt_pi_iff]
    rcases (Complex.mem_slitPlane_iff.mp hw) with hre | him
    · exact Or.inl hre.le
    · exact Or.inr him
  have hscale : Tendsto (fun eps : ℝ ↦ (‖w‖ / r) * eps)
      (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_iff_comap, comap_mulLeft_nhdsGT_zero (div_pos hw0 hr)]
  have hendpoint : Tendsto
      (fun eps : ℝ ↦ CompositionContinuation.continued (first :: suffix)
        (1 - (eps : ℂ) * w))
      (𝓝[>] 0) (𝓝 (CompositionBoundary.zeta first suffix : ℂ)) := by
    let F : ℝ → ℝ → ℂ := fun eps θ ↦
      CompositionContinuation.continued (first :: suffix)
        (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))
    have hpositive : Tendsto (fun eps : ℝ ↦ F eps 0) (𝓝[>] 0)
        (𝓝 (CompositionBoundary.zeta first suffix : ℂ)) := by
      simpa [F, Complex.exp_zero] using hpositiveRay first suffix hfirst r hr
    have hcommonRay : Tendsto (fun eps : ℝ ↦ F eps (Complex.arg w))
        (𝓝[>] 0) (𝓝 (CompositionBoundary.zeta first suffix : ℂ)) := by
      by_cases hθ : 0 ≤ Complex.arg w
      · have hvanish := ordinary_angular_subarc_vanishes first suffix hfirst ρ D N
          hρ hD hbound r 0 (Complex.arg w) hr hrρ
          (by linarith [Real.pi_pos]) hargpos hθ
        have hcombined : Tendsto
            (fun eps : ℝ ↦ (∫ x in (0 : ℝ)..Complex.arg w,
              (-I) * (((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) *
                CompositionContinuation.continued
                  (⟨(first : ℕ) - 1, by omega⟩ :: suffix)
                    (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) /
                  (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I))) + F eps 0)
            (𝓝[>] 0) (𝓝 (0 + (CompositionBoundary.zeta first suffix : ℂ))) :=
          hvanish.add hpositive
        have hformula : ∀ᶠ eps : ℝ in 𝓝[>] 0,
            F eps (Complex.arg w) = (∫ x in (0 : ℝ)..Complex.arg w,
              (-I) * (((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) *
                CompositionContinuation.continued
                  (⟨(first : ℕ) - 1, by omega⟩ :: suffix)
                    (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) /
                  (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I))) + F eps 0 := by
          filter_upwards [Ioo_mem_nhdsGT
            (show 0 < min 1 (1 / (2 * r)) by positivity)] with eps heps
          have hprod : 0 < eps * r := mul_pos heps.1 hr
          have hprod1 : eps * r < 1 :=
            (mul_lt_of_lt_one_left hr (heps.2.trans_le (min_le_left _ _))).trans hr1
          have hftc := hangularFTC first suffix hfirst (eps * r) 0 (Complex.arg w)
            hprod hprod1 (by linarith [Real.pi_pos]) hargpos hθ
          change (∫ x in (0 : ℝ)..Complex.arg w,
              (-I) * (((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) *
                CompositionContinuation.continued
                  (⟨(first : ℕ) - 1, by omega⟩ :: suffix)
                    (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) /
                  (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I))) =
                F eps (Complex.arg w) - F eps 0 at hftc
          rw [hftc]
          ring
        simpa [F] using hcombined.congr' (Filter.EventuallyEq.symm hformula)
      · have hθle : Complex.arg w ≤ 0 := le_of_not_ge hθ
        have hvanish := ordinary_angular_subarc_vanishes first suffix hfirst ρ D N
          hρ hD hbound r (Complex.arg w) 0 hr hrρ hargneg
          (by linarith [Real.pi_pos]) hθle
        have hcombined : Tendsto
            (fun eps : ℝ ↦ F eps 0 - (∫ x in Complex.arg w..(0 : ℝ),
              (-I) * (((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) *
                CompositionContinuation.continued
                  (⟨(first : ℕ) - 1, by omega⟩ :: suffix)
                    (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) /
                  (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I))))
            (𝓝[>] 0) (𝓝 ((CompositionBoundary.zeta first suffix : ℂ) - 0)) :=
          hpositive.sub hvanish
        have hformula : ∀ᶠ eps : ℝ in 𝓝[>] 0,
            F eps (Complex.arg w) = F eps 0 - (∫ x in Complex.arg w..(0 : ℝ),
              (-I) * (((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) *
                CompositionContinuation.continued
                  (⟨(first : ℕ) - 1, by omega⟩ :: suffix)
                    (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) /
                  (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I))) := by
          filter_upwards [Ioo_mem_nhdsGT
            (show 0 < min 1 (1 / (2 * r)) by positivity)] with eps heps
          have hprod : 0 < eps * r := mul_pos heps.1 hr
          have hprod1 : eps * r < 1 :=
            (mul_lt_of_lt_one_left hr (heps.2.trans_le (min_le_left _ _))).trans hr1
          have hftc := hangularFTC first suffix hfirst (eps * r) (Complex.arg w) 0
            hprod hprod1 hargneg (by linarith [Real.pi_pos]) hθle
          change (∫ x in Complex.arg w..(0 : ℝ),
              (-I) * (((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) *
                CompositionContinuation.continued
                  (⟨(first : ℕ) - 1, by omega⟩ :: suffix)
                    (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) /
                  (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I))) =
                F eps 0 - F eps (Complex.arg w) at hftc
          rw [hftc]
          ring
        simpa [F] using hcombined.congr' (Filter.EventuallyEq.symm hformula)
    have h := hcommonRay.comp hscale
    apply h.congr'
    filter_upwards with eps
    have hpoint :
        (((((‖w‖ / r) * eps) * r : ℝ) : ℂ) *
            Complex.exp ((Complex.arg w : ℂ) * I)) = (eps : ℂ) * w := by
      calc
        (((((‖w‖ / r) * eps) * r : ℝ) : ℂ) *
            Complex.exp ((Complex.arg w : ℂ) * I)) =
            (eps : ℂ) * ((‖w‖ : ℂ) *
              Complex.exp ((Complex.arg w : ℂ) * I)) := by
          push_cast
          field_simp [ne_of_gt hr]
        _ = (eps : ℂ) * w := by rw [Complex.norm_mul_exp_arg_mul_I]
    exact congrArg (fun u : ℂ ↦
      CompositionContinuation.continued (first :: suffix) (1 - u)) hpoint
  let E : ℂ → ℂ := fun u ↦
    -CompositionContinuation.continued
      (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - u)
  let integrand : ℝ → ℂ := fun t ↦
    w * (E ((t : ℂ) * w) / (1 - (t : ℂ) * w))
  let Ecut : ℂ → ℂ := fun u ↦
    if u = 0 then E u else if u ∈ Complex.slitPlane ∧ ‖u‖ < ρ then E u else 0
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hw0)
  have hw1 : ‖w‖ < 1 := hwρ.trans hρ1
  have hEcut : ∀ u : ℂ, u ≠ 0 →
      ‖Ecut u‖ ≤ D * ‖u‖ ^ 0 * (1 + ‖-Complex.log u‖) ^ N := by
    intro u hu
    simp only [Ecut, if_neg hu]
    by_cases hcut : u ∈ Complex.slitPlane ∧ ‖u‖ < ρ
    · rw [if_pos hcut, pow_zero, mul_one]
      simpa [E, norm_neg] using hbound u hcut.1 (norm_pos_iff.mpr hu) hcut.2
    · rw [if_neg hcut, norm_zero]
      positivity
  have hline : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Ecut ((t : ℂ) * w) = E ((t : ℂ) * w) := by
    intro t ht
    have htne : (t : ℂ) * w ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht.1))
      (norm_ne_zero_iff.mp (ne_of_gt hw0))
    simp only [Ecut, if_neg htne]
    apply if_pos
    have htw : (t : ℂ) * w ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hw ⊢
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.mul_im, add_zero]
      exact hw.imp (fun h ↦ mul_pos ht.1 h) (mul_ne_zero ht.1.ne')
    refine ⟨htw, ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans_lt hwρ
  have hmajor : IntervalIntegrable
      (fun t : ℝ ↦
        (D * ‖w‖ ^ (0 + 1) * (1 - ‖w‖)⁻¹) *
          (t ^ (1 - 1) *
            (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ N))
      MeasureTheory.volume 0 1 := by
    exact (radial_majorant_integrable ‖-Complex.log w‖ 1 N
      (norm_nonneg _) (by omega)).const_mul
        (D * ‖w‖ ^ (0 + 1) * (1 - ‖w‖)⁻¹)
  have hint : IntervalIntegrable integrand MeasureTheory.volume 0 1 := by
    apply hmajor.mono_fun'
    · have hcont : ContinuousOn integrand (Set.Ioc (0 : ℝ) 1) := by
        intro t ht
        have htw : (t : ℂ) * w ∈ Complex.slitPlane := by
          rw [Complex.mem_slitPlane_iff] at hw ⊢
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
            sub_zero, Complex.mul_im, add_zero]
          exact hw.imp (fun h ↦ mul_pos ht.1 h) (mul_ne_zero ht.1.ne')
        have hω : 1 - (t : ℂ) * w ∈ CompositionContinuation.omega := by
          simpa [CompositionContinuation.omega] using htw
        have hden : (1 : ℂ) - (t : ℂ) * w ≠ 0 := by
          intro hzero
          have hone : (t : ℂ) * w = 1 := (sub_eq_zero.mp hzero).symm
          have : ‖(t : ℂ) * w‖ = 1 := by rw [hone, norm_one]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] at this
          nlinarith [mul_le_of_le_one_left (norm_nonneg w) ht.2]
        have hinner : ContinuousAt
            (fun s : ℝ ↦ (1 : ℂ) - (s : ℂ) * w) t := by fun_prop
        have houter : ContinuousAt (fun u : ℂ ↦
            -CompositionContinuation.continued
              (⟨(first : ℕ) - 1, by omega⟩ :: suffix) u)
            (1 - (t : ℂ) * w) :=
          (((CompositionSlit.result).2.1 _).1 _ hω).continuousAt.neg
        have hnum : ContinuousAt (fun s : ℝ ↦ E ((s : ℂ) * w)) t := by
          exact ContinuousAt.comp
            (g := fun u : ℂ ↦ -CompositionContinuation.continued
              (⟨(first : ℕ) - 1, by omega⟩ :: suffix) u)
            (f := fun s : ℝ ↦ (1 : ℂ) - (s : ℂ) * w) houter hinner
        exact (continuousAt_const.mul (hnum.div hinner hden)).continuousWithinAt
      simpa [Set.uIoc_of_le zero_le_one] using
        hcont.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using ht
      have hcut := hline t ht'
      change ‖w * (E ((t : ℂ) * w) / (1 - (t : ℂ) * w))‖ ≤ _
      rw [← hcut]
      simpa only [Nat.sub_self, pow_zero, one_mul, mul_assoc,
        mul_left_comm, mul_comm] using
        radial_one_sub_bound Ecut D 0 N hD w hwne hw1 hEcut t ht'
  have hprimitive : ContinuousOn
      (fun eps : ℝ ↦ ∫ t in eps..1, integrand t) (Set.uIcc (0 : ℝ) 1) := by
    apply intervalIntegral.continuousOn_primitive_interval_left
    simpa [Set.uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hint
  have huIcc : Set.uIcc (0 : ℝ) 1 ∈ 𝓝[>] 0 := by
    apply mem_of_superset (Ioo_mem_nhdsGT zero_lt_one)
    intro eps heps
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨heps.1.le, heps.2.le⟩
  have hintegralLimit : Tendsto
      (fun eps : ℝ ↦ ∫ t in eps..1, integrand t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, integrand t)) :=
    (hprimitive 0 Set.left_mem_uIcc).mono_of_mem_nhdsWithin huIcc
  have hformula : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      (∫ t in eps..1, integrand t) =
        CompositionContinuation.continued (first :: suffix) (1 - w) -
          CompositionContinuation.continued (first :: suffix)
            (1 - (eps : ℂ) * w) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with eps heps
    have hint' : IntervalIntegrable integrand MeasureTheory.volume eps 1 :=
      IntervalIntegrable.mono hint (by
        rw [Set.uIcc_of_le heps.2.le, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc heps.1.le le_rfl) le_rfl
    have hderiv : ∀ t ∈ Set.uIcc eps 1,
        HasDerivAt
          (fun s : ℝ ↦ CompositionContinuation.continued
            (first :: suffix) (1 - (s : ℂ) * w)) (integrand t) t := by
      intro t ht
      rw [Set.uIcc_of_le heps.2.le] at ht
      have ht0 : 0 < t := heps.1.trans_le ht.1
      have htw : (t : ℂ) * w ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff] at hw ⊢
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero, Complex.mul_im, add_zero]
        exact hw.imp (fun h ↦ mul_pos ht0 h) (mul_ne_zero ht0.ne')
      have htwnorm : ‖(t : ℂ) * w‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans_lt hw1
      have hline : HasDerivAt (fun u : ℂ ↦ u * w) w (t : ℂ) := by
        simpa using (hasDerivAt_id (t : ℂ)).mul_const w
      have hcomp := (hordinaryDeriv first suffix hfirst ((t : ℂ) * w)
        (fun h ↦ by simpa [h] using htwnorm)
        (by simpa [CompositionContinuation.omega] using htw)).comp (t : ℂ) hline
      have hreal := hcomp.comp_ofReal
      simpa only [integrand, E, Function.comp_def, mul_comm] using hreal
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint'
    simpa [integrand] using hftc
  have hright : Tendsto
      (fun eps : ℝ ↦
        CompositionContinuation.continued (first :: suffix) (1 - w) -
          CompositionContinuation.continued (first :: suffix) (1 - (eps : ℂ) * w))
      (𝓝[>] 0)
      (𝓝 (CompositionContinuation.continued (first :: suffix) (1 - w) -
        (CompositionBoundary.zeta first suffix : ℂ))) :=
    tendsto_const_nhds.sub hendpoint
  have heq := tendsto_nhds_unique hintegralLimit
    (hright.congr' (Filter.EventuallyEq.symm hformula))
  simpa [E, integrand] using heq
private theorem ordinary_admissible_remainder_step : ∀ (first : ℕ+) (suffix : List ℕ+)
    (hfirst : 1 < (first : ℕ)) (ρ D : ℝ) (N : ℕ),
    0 < ρ → ρ < 1 → 0 ≤ D →
    (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
          (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - w)‖ ≤
        D * (1 + ‖-Complex.log w‖) ^ N) →
      admissibleRemainder first suffix := by
  intro first suffix hfirst ρ D N hρ hρ1 hD hbound
  let ρ' : ℝ := min ρ (1 / 2)
  let K : ℝ := ∫ t in (0 : ℝ)..1, t ^ 0 * (1 + (-Real.log t)) ^ N
  let C : ℝ := 2 * D * K
  have hρ'0 : 0 < ρ' := by dsimp [ρ']; positivity
  have hρ'1 : ρ' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hK : 0 ≤ K := by
    dsimp [K]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using ht
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht'.1 ht'.2
    exact mul_nonneg (pow_nonneg ht'.1 0) (pow_nonneg (by linarith) N)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨hfirst, ρ', C, N, hρ'0, hρ'1, hC, ?_⟩
  intro w hw hw0 hwρ'
  have hwρ : ‖w‖ < ρ := hwρ'.trans_le (min_le_left _ _)
  have hwHalf : ‖w‖ < 1 / 2 := hwρ'.trans_le (min_le_right _ _)
  have hw1 : ‖w‖ < 1 := hwHalf.trans (by norm_num)
  let E : ℂ → ℂ := fun u ↦
    -CompositionContinuation.continued
      (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - u)
  let Ecut : ℂ → ℂ := fun u ↦
    if u = 0 then E u else if u ∈ Complex.slitPlane ∧ ‖u‖ < ρ then E u else 0
  have hEcut : ∀ u : ℂ, u ≠ 0 →
      ‖Ecut u‖ ≤ D * ‖u‖ ^ 0 * (1 + ‖-Complex.log u‖) ^ N := by
    intro u hu
    simp only [Ecut, if_neg hu]
    by_cases hcut : u ∈ Complex.slitPlane ∧ ‖u‖ < ρ
    · rw [if_pos hcut, pow_zero, mul_one]
      simpa [E, norm_neg] using hbound u hcut.1 (norm_pos_iff.mpr hu) hcut.2
    · rw [if_neg hcut, norm_zero]
      positivity
  have hline : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Ecut ((t : ℂ) * w) = E ((t : ℂ) * w) := by
    intro t ht
    have htne : (t : ℂ) * w ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht.1))
      (norm_ne_zero_iff.mp (ne_of_gt hw0))
    simp only [Ecut, if_neg htne]
    apply if_pos
    have htw : (t : ℂ) * w ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hw ⊢
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.mul_im, add_zero]
      exact hw.imp (fun h ↦ mul_pos ht.1 h) (mul_ne_zero ht.1.ne')
    refine ⟨htw, ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans_lt hwρ
  have huniform := radial_one_sub_uniform_bound Ecut D 0 N hD w
    (norm_ne_zero_iff.mp (ne_of_gt hw0)) hw1 hEcut
  have hreplace :
      (∫ t in (0 : ℝ)..1,
        w * (Ecut ((t : ℂ) * w) / (1 - (t : ℂ) * w))) =
      ∫ t in (0 : ℝ)..1,
        w * (E ((t : ℂ) * w) / (1 - (t : ℂ) * w)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      simp [Ecut]
    · rw [Set.uIcc_of_le zero_le_one] at ht
      have ht' : t ∈ Set.Ioc (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
      change w * (Ecut ((t : ℂ) * w) / (1 - (t : ℂ) * w)) =
        w * (E ((t : ℂ) * w) / (1 - (t : ℂ) * w))
      rw [hline t ht']
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - ‖w‖ := by linarith
    have hrecip := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
    norm_num [one_div] at hrecip
    exact hrecip
  have hidentity := ordinary_integral_identity first suffix hfirst ρ D N
    hρ hρ1 hD hbound w hw hw0 hwρ
  rw [← hidentity, ← hreplace]
  calc
    ‖∫ t in (0 : ℝ)..1,
        w * (Ecut ((t : ℂ) * w) / (1 - (t : ℂ) * w))‖ ≤
        D * ‖w‖ ^ (0 + 1) * (1 + ‖-Complex.log w‖) ^ N *
          (1 - ‖w‖)⁻¹ * K := by simpa [K] using huniform
    _ ≤ D * ‖w‖ * (1 + ‖-Complex.log w‖) ^ N * 2 * K := by
      simp only [zero_add, pow_one]
      gcongr
    _ = C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ N := by
      dsimp [C]
      ring

end D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksOrdinaryTransport
