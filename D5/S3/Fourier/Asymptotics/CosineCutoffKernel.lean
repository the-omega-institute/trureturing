/- GID: D5/S3/Fourier/Asymptotics/CosineCutoffKernel
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineCutoffKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The closed finite reciprocal-frequency symbol has the actual cosine cutoff as its ordinary inverse Fourier integral, with logarithmic zero-frequency and null-band endpoint normalization. -/

import Mathlib.Analysis.Fourier.FourierTransform
import D5.S3.Quantum.Analysis.FourierWindowFiniteRank
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Set Filter FourierTransform
open scoped FourierTransform ENNReal Topology SchwartzMap
noncomputable section
namespace D5.S3.Fourier.Asymptotics.CosineCutoffKernel
set_option autoImplicit false
set_option relaxedAutoImplicit false
def kernel (c N x : ℝ) : ℝ := -2 * ∫ t in c..N, Real.cos (t*x) / t
def symbol (c N ξ : ℝ) : ℂ :=
 if c/(2*Real.pi) ≤ |ξ| ∧ |ξ| ≤ N/(2*Real.pi) then ((-(1/|ξ|):ℝ):ℂ) else 0
private def band (c N : ℝ) : ℝ → ℂ :=
 (Icc (c/(2*Real.pi)) (N/(2*Real.pi))).indicator (fun ξ => ((-(1/ξ):ℝ):ℂ))
private theorem symbol_pair (c N : ℝ) (hc : 0 < c) :
 symbol c N = fun ξ => band c N ξ + band c N (-ξ) := by
 have ha : 0 < c/(2*Real.pi) := div_pos hc (by positivity)
 funext ξ
 by_cases hx : 0 ≤ ξ
 · have hn : ¬ (c/(2*Real.pi) ≤ -ξ ∧ -ξ ≤ N/(2*Real.pi)) := by
     intro h; linarith [h.1]
   simp [symbol, band, abs_of_nonneg hx, hn, Set.indicator_apply]
 · have hx' : ξ < 0 := lt_of_not_ge hx
   have hn : ¬ (c/(2*Real.pi) ≤ ξ ∧ ξ ≤ N/(2*Real.pi)) := by
     intro h; linarith [h.1]
   simp [symbol, band, abs_of_neg hx', hn, Set.indicator_apply]
private theorem band_integrable (c N : ℝ) (hc : 0 < c) : Integrable (band c N) := by
 have ha : 0 < c/(2*Real.pi) := div_pos hc (by positivity)
 have hcont : ContinuousOn (fun ξ : ℝ => ((-(1/ξ):ℝ):ℂ))
     (Icc (c/(2*Real.pi)) (N/(2*Real.pi))) := by
   apply Complex.continuous_ofReal.comp_continuousOn
   apply ContinuousOn.neg
   apply continuousOn_const.div continuousOn_id
   intro ξ hξ
   exact ne_of_gt (ha.trans_le hξ.1)
 exact hcont.integrableOn_Icc.integrable_indicator measurableSet_Icc
private theorem phase_pair (θ : ℝ) :
 Complex.exp ((θ:ℂ)*Complex.I) + Complex.exp ((-θ:ℂ)*Complex.I) =
     (2 * Real.cos θ : ℝ) := by
 rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos, Complex.cos]
 ring
private theorem inverse_integral (c N x : ℝ) (hc : 0 < c) (hN : c ≤ N) :
 (𝓕⁻ (symbol c N)) x = (kernel c N x : ℂ) := by
 let d : ℝ := 2*Real.pi
 let A : ℝ := c/d
 let B : ℝ := N/d
 let P : ℝ → ℂ := fun ξ => Complex.exp (((d*(ξ*x):ℝ):ℂ)*Complex.I)
 have hd : 0 < d := by dsimp [d]; positivity
 have hAB : A ≤ B := (div_le_div_iff_of_pos_right hd).mpr hN
 have hp := band_integrable c N hc
 have hi (g : ℝ → ℂ) (hg : Integrable g) : Integrable (fun ξ => P ξ * g ξ) := by
   simpa [P,d,Real.inner_apply,mul_neg,neg_neg,Circle.smul_def,smul_eq_mul,
     Real.fourierChar_apply,mul_comm] using (Real.fourierIntegral_convergent_iff (f:=g) (-x)).mpr hg
 have hi1 := hi (band c N) hp
 have hi2 := hi (fun ξ => band c N (-ξ)) hp.comp_neg
 have hi3 : Integrable (fun ξ => P (-ξ)*band c N ξ) := by
   simpa using hi2.comp_neg
 have hn : (∫ ξ : ℝ, P ξ*band c N (-ξ)) = ∫ ξ : ℝ, P (-ξ)*band c N ξ := by
   simpa using (integral_neg_eq_self (fun ξ : ℝ => P ξ*band c N (-ξ)) volume).symm
 have he : (fun ξ => P ξ*band c N ξ + P (-ξ)*band c N ξ) =
     (Icc A B).indicator (fun ξ => ((-2*Real.cos (d*(ξ*x))/ξ : ℝ):ℂ)) := by
   funext ξ
   by_cases hξ : ξ ∈ Icc A B
   · have hξ' : ξ ∈ Icc (c/(2*Real.pi)) (N/(2*Real.pi)) := hξ
     simp only [band,indicator_of_mem hξ',indicator_of_mem hξ]
     rw [← add_mul]
     have heP : P ξ+P (-ξ) = (2*Real.cos (d*(ξ*x)):ℝ) := by
       dsimp [P]
       convert phase_pair (d*(ξ*x)) using 1
       push_cast
       congr 2
       ring
     rw [heP]
     push_cast
     ring
   · have hξ' : ξ ∉ Icc (c/(2*Real.pi)) (N/(2*Real.pi)) := hξ
     simp [band,indicator_of_notMem hξ',indicator_of_notMem hξ]
 have hs : (∫ ξ in A..B, Real.cos (d*(ξ*x))/ξ) =
     ∫ t in c..N, Real.cos (t*x)/t := by
   calc
     (∫ ξ in A..B, Real.cos (d*(ξ*x))/ξ) =
         d * ∫ ξ in A..B, Real.cos ((d*ξ)*x)/(d*ξ) := by
       rw [← intervalIntegral.integral_const_mul]
       apply intervalIntegral.integral_congr
       intro ξ hξ
       dsimp only
       rw [mul_assoc]
       field_simp [hd.ne']
       congr 2
       dsimp [d]
       ring
     _ = ∫ t in c..N, Real.cos (t*x)/t := by
       have h := intervalIntegral.mul_integral_comp_mul_left
         (a:=A) (b:=B) (f:=fun t : ℝ => Real.cos (t*x)/t) d
       simpa [A,B,mul_div_cancel₀ _ hd.ne'] using h
 rw [Real.fourierInv_eq']
 simp only [Real.inner_apply,smul_eq_mul]
 change (∫ ξ : ℝ, P ξ*symbol c N ξ) = _
 rw [symbol_pair c N hc]
 simp only [mul_add]
 rw [integral_add hi1 hi2,hn,← integral_add hi1 hi3,he,integral_indicator measurableSet_Icc,
   integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hAB,
   intervalIntegral.integral_ofReal]
 rw [show (∫ ξ in A..B, -2*Real.cos (d*(ξ*x))/ξ) =
     -2*(∫ ξ in A..B, Real.cos (d*(ξ*x))/ξ) by
   simp only [mul_div_assoc,intervalIntegral.integral_const_mul]]
 rw [hs]
 rfl


private theorem symbol_bound (c N ξ : ℝ) (hc : 0 < c) : ‖symbol c N ξ‖ ≤ 2*Real.pi/c := by
 have hd : 0 < 2*Real.pi := by positivity
 dsimp [symbol]
 split_ifs with h
 · have hx : 0 < |ξ| := (div_pos hc hd).trans_le h.1
   have hb := one_div_le_one_div_of_le (div_pos hc hd) h.1
   simpa [Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_div,abs_abs,one_div,inv_div] using hb
 · simp only [norm_zero]
   positivity

/-- Ordinary inverse integration of the finite hard symbol, with the logarithmic and null-band boundaries. -/
theorem result : ∀ c N : ℝ, 0 < c → c ≤ N →
    Measurable (symbol c N) ∧ Integrable (symbol c N) ∧ MemLp (symbol c N) 2 volume ∧
    (∀ ξ : ℝ, ‖symbol c N ξ‖ ≤ 2*Real.pi/c) ∧
    (∀ M : ℝ, N ≤ M → ∀ ξ : ℝ, ‖symbol c M ξ - symbol c N ξ‖ ≤ 2*Real.pi/N) ∧
    (∀ x : ℝ, (𝓕⁻ (symbol c N)) x = (kernel c N x : ℂ)) ∧
    kernel c N 0 = -2 * Real.log (N/c) ∧
    (c = N → (∀ x : ℝ, kernel c N x = 0) ∧
      (∀ (rho f : ℝ → ℝ) (x : ℝ), (∫ y : ℝ, kernel c N (x-y)*f y*rho y) = 0) ∧
      symbol c N =ᵐ[volume] (fun _ : ℝ => (0 : ℂ)) ∧
      symbol c N (c/(2*Real.pi)) ≠ 0 ∧ symbol c N (-(c/(2*Real.pi))) ≠ 0) := by
  intro c N hc hN
  have hm : Measurable (symbol c N) := by
    have habs : Measurable (fun ξ : ℝ => |ξ|) := continuous_abs.measurable
    have hm : MeasurableSet {ξ : ℝ | c/(2*Real.pi) ≤ |ξ| ∧ |ξ| ≤ N/(2*Real.pi)} :=
      (measurableSet_le measurable_const habs).inter
        (measurableSet_le habs measurable_const)
    exact (Complex.measurable_ofReal.comp ((measurable_const.div habs).neg)).piecewise hm measurable_const
  have hi : Integrable (symbol c N) := by
    rw [symbol_pair c N hc]
    exact (band_integrable c N hc).add (band_integrable c N hc).comp_neg
  have hL2 : MemLp (symbol c N) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
    have hbound : ∀ ξ : ℝ, ‖‖symbol c N ξ‖‖ ≤ 2*Real.pi/c := by
      intro ξ
      simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using symbol_bound c N ξ hc
    have hp := hi.norm.mul_bdd hi.aestronglyMeasurable.norm (Filter.Eventually.of_forall hbound)
    simpa only [pow_two] using hp
  refine ⟨hm,hi,hL2,fun ξ => symbol_bound c N ξ hc,?_,fun x => inverse_integral c N x hc hN,?_,?_⟩
  · intro M hM ξ
    have hd : 0 < 2*Real.pi := by positivity
    have hNp : 0 < N := hc.trans_le hN
    by_cases hs : c/(2*Real.pi) ≤ |ξ| ∧ |ξ| ≤ N/(2*Real.pi)
    · have hl : c/(2*Real.pi) ≤ |ξ| ∧ |ξ| ≤ M/(2*Real.pi) :=
        ⟨hs.1,hs.2.trans ((div_le_div_iff_of_pos_right hd).mpr hM)⟩
      simp [symbol,hs,hl,le_of_lt (div_pos hd hNp)]
    · by_cases hl : c/(2*Real.pi) ≤ |ξ| ∧ |ξ| ≤ M/(2*Real.pi)
      · have hn : N/(2*Real.pi) ≤ |ξ| := by
          apply le_of_lt
          apply lt_of_not_ge
          intro hh
          exact hs ⟨hl.1,hh⟩
        have hnstrict : ¬ |ξ| ≤ N/(2*Real.pi) := fun hh => hs ⟨hl.1,hh⟩
        have hb := one_div_le_one_div_of_le (div_pos hNp hd) hn
        simpa [symbol,hl,hnstrict,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_div,abs_abs,one_div,inv_div] using hb
      · simp [symbol,hs,hl,le_of_lt (div_pos hd hNp)]
  · simp only [kernel,mul_zero,Real.cos_zero]
    rw [integral_one_div_of_pos hc (hc.trans_le hN)]
  · intro h
    subst N
    have hzero : ∀ x : ℝ, kernel c c x = 0 := by intro x; simp [kernel]
    have hae : symbol c c =ᵐ[volume] (fun _ : ℝ => (0 : ℂ)) := by
      let A := c/(2*Real.pi)
      have ha : 0 < A := div_pos hc (by positivity)
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton A),
          compl_mem_ae_iff.mpr (measure_singleton (-A))] with ξ hx hy
      have hx' : ξ ≠ A := by simpa using hx
      have hy' : ξ ≠ -A := by simpa using hy
      have hn : ¬(A ≤ |ξ| ∧ |ξ| ≤ A) := by
        intro h
        have he : |ξ| = A := le_antisymm h.2 h.1
        rcases le_total 0 ξ with hpos | hneg
        · apply hx'
          simpa [abs_of_nonneg hpos] using he
        · apply hy'
          rw [abs_of_nonpos hneg] at he
          linarith
      simp [symbol,show c/(2*Real.pi) = A from rfl,hn]
    refine ⟨hzero,?_,hae,?_⟩
    · intro rho f x
      simp only [hzero,zero_mul,integral_zero]
    ·
      have ha : 0 < c/(2*Real.pi) := div_pos hc (by positivity)
      constructor
      · simp [symbol,abs_of_pos ha,hc.ne']
      · simp [symbol,abs_neg,abs_of_pos ha,hc.ne']


local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩

private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev HE := Lp (α := E1) ℂ (2 : ℝ≥0∞) (volume : Measure E1)
private abbrev HR := Lp (α := ℝ) ℂ (2 : ℝ≥0∞) (volume : Measure ℝ)
private def FE : HE ≃ₗᵢ[ℂ] HE := Lp.fourierTransformₗᵢ E1 ℂ
private def FR : HR ≃ₗᵢ[ℂ] HR := Lp.fourierTransformₗᵢ ℝ ℂ

private def mask (S : Set E1) (hS : MeasurableSet S)
    (hfin : (volume : Measure E1) S ≠ ∞) : HE →L[ℂ] HE :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL (volume : Measure E1)
    (∞ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞)
    (indicatorConstLp ∞ hS hfin (1 : ℂ))

private theorem mask_coe (S : Set E1) (hS : MeasurableSet S)
    (hfin : (volume : Measure E1) S ≠ ∞) (f : HE) :
    ⇑(mask S hS hfin f) =ᵐ[volume] S.indicator (⇑f) := by
  have hmul := (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder
    (r := (2 : ℝ≥0∞)) (indicatorConstLp ∞ hS hfin (1 : ℂ)) f
  have hind : ⇑(indicatorConstLp ∞ hS hfin (1 : ℂ)) =ᵐ[volume]
      S.indicator (fun _ : E1 => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  change ⇑((ContinuousLinearMap.lsmul ℂ ℂ).holder (2 : ℝ≥0∞)
    (indicatorConstLp ∞ hS hfin (1 : ℂ)) f) =ᵐ[volume] _
  filter_upwards [hmul, hind] with x hx hi
  rw [hx, hi]
  by_cases hs : x ∈ S <;>
    simp [hs, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- The public window identity with bounded input; countable output balls remove MB. -/
private theorem forward_bounded_E1 (g : E1 → ℂ) (hg : MemLp g 2 volume)
    (R : ℝ) (hR : 0 ≤ R) (hs : ∀ x : E1, R < ‖x‖ → g x = 0) :
    ⇑(FE (hg.toLp g)) =ᵐ[volume] (𝓕 g : E1 → ℂ) := by
  let A : Set E1 := Metric.closedBall (0 : E1) R
  have hA : MeasurableSet A := measurableSet_closedBall
  have hAfin : (volume : Measure E1) A ≠ ∞ :=
    (isCompact_closedBall (0 : E1) R).measure_ne_top
  let f : HE := hg.toLp g
  have hfix : mask A hA hAfin f = f := by
    apply Lp.ext
    filter_upwards [mask_coe A hA hAfin f, hg.coeFn_toLp] with x hm hx
    rw [hm]
    by_cases ha : x ∈ A
    · simp only [Set.indicator_of_mem ha]
    · have hRx : R < ‖x‖ := by
        simpa only [A, Metric.mem_closedBall, dist_zero_right, not_le] using ha
      rw [Set.indicator_of_notMem ha, hx, hs x hRx]
  have hIntegral (ξ : E1) :
      (∫ x in A, Complex.exp ((((-2 * Real.pi : ℝ) : ℂ) * Complex.I) *
          ((inner ℝ x ξ : ℝ) : ℂ)) * f x) = (𝓕 g : E1 → ℂ) ξ := by
    rw [← integral_indicator hA, Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    by_cases ha : x ∈ A
    · rw [Set.indicator_of_mem ha, hx]
      simp only [smul_eq_mul]
      congr 2 <;> push_cast <;> ring
    · have hRx : R < ‖x‖ := by
        simpa only [A, Metric.mem_closedBall, dist_zero_right, not_le] using ha
      simp only [Set.indicator_of_notMem ha, hs x hRx, smul_zero]
  have hlocal (j : ℕ) : ∀ᵐ ξ : E1 ∂volume,
      ‖ξ‖ ≤ (j : ℝ) → (FE f) ξ = (𝓕 g : E1 → ℂ) ξ := by
    let B : Set E1 := Metric.closedBall (0 : E1) (j : ℝ)
    have hB : MeasurableSet B := measurableSet_closedBall
    have hBfin : (volume : Measure E1) B ≠ ∞ :=
      (isCompact_closedBall (0 : E1) (j : ℝ)).measure_ne_top
    have hsup :=
      D5.S3.Quantum.Analysis.FourierWindowFiniteRank.fourier_window_finite_rank_approximation
        1 A B R (j : ℝ) hR (by positivity) hA hB hAfin hBfin
        (by intro x hx; simpa only [A, Metric.mem_closedBall, dist_zero_right] using hx)
        (by intro ξ hξ; simpa only [B, Metric.mem_closedBall, dist_zero_right] using hξ)
    rcases hsup with ⟨vin, vout, hvin, hvout, hinner, hrest⟩
    have hwindow : ⇑(mask B hB hBfin (FE (mask A hA hAfin f))) =ᵐ[volume]
        B.indicator (fun ξ : E1 => ∫ x in A,
          Complex.exp ((((-2 * Real.pi : ℝ) : ℂ) * Complex.I) *
            ((inner ℝ x ξ : ℝ) : ℂ)) * f x) := hrest.1 f
    rw [hfix] at hwindow
    filter_upwards [hwindow, mask_coe B hB hBfin (FE f)] with ξ hw hm
    intro hξ
    have hb : ξ ∈ B := by
      simpa only [B, Metric.mem_closedBall, dist_zero_right] using hξ
    rw [hm, Set.indicator_of_mem hb, Set.indicator_of_mem hb] at hw
    exact hw.trans (hIntegral ξ)
  have hall : ∀ᵐ ξ : E1 ∂volume, ∀ j : ℕ,
      ‖ξ‖ ≤ (j : ℝ) → (FE f) ξ = (𝓕 g : E1 → ℂ) ξ := ae_all_iff.mpr hlocal
  filter_upwards [hall] with ξ hξ
  obtain ⟨j, hj⟩ := exists_nat_gt ‖ξ‖
  exact hξ j hj.le

private def coord : ℝ ≃ₗᵢ[ℝ] E1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
private def pull1 : HE →ₗᵢ[ℂ] HR :=
  Lp.compMeasurePreservingₗᵢ ℂ (coord : ℝ → E1) coord.measurePreserving
private def comp1 (ψ : 𝓢(E1, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coord.toContinuousLinearEquiv ψ

private theorem pull1_coe (f : HE) :
    ⇑(pull1 f) =ᵐ[volume] (fun x : ℝ => f (coord x)) :=
  Lp.coeFn_compMeasurePreserving f coord.measurePreserving

private theorem pull1_schwartz (ψ : 𝓢(E1, ℂ)) :
    pull1 (ψ.toLp 2 volume) = (comp1 ψ).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [pull1_coe (ψ.toLp 2 volume),
    coord.measurePreserving.quasiMeasurePreserving.ae_eq (ψ.coeFn_toLp 2 volume),
    (comp1 ψ).coeFn_toLp 2 volume] with x hp hψ hc
  change (pull1 (ψ.toLp 2 volume)) x = ((comp1 ψ).toLp 2 volume) x
  calc
    _ = (ψ.toLp 2 volume) (coord x) := hp
    _ = ψ (coord x) := hψ
    _ = (comp1 ψ) x := rfl
    _ = _ := hc.symm

private theorem fourier_pull1 (f : HE) : FR (pull1 f) = pull1 (FE f) := by
  apply DenseRange.induction_on (p := fun f : HE => FR (pull1 f) = pull1 (FE f))
    (SchwartzMap.denseRange_toLpCLM (E := E1) (F := ℂ) (p := 2)
      (μ := (volume : Measure E1)) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (FR.continuous.comp pull1.continuous)
      (pull1.continuous.comp FE.continuous)
  intro ψ
  change FR (pull1 (ψ.toLp 2 volume)) = pull1 (FE (ψ.toLp 2 volume))
  have hSch : (𝓕 (comp1 ψ) : 𝓢(ℝ, ℂ)) = comp1 (𝓕 ψ : 𝓢(E1, ℂ)) := by
    ext x
    change (𝓕 ((ψ : E1 → ℂ) ∘ coord) : ℝ → ℂ) x =
      (𝓕 (ψ : E1 → ℂ) : E1 → ℂ) (coord x)
    exact Real.fourier_comp_linearIsometry coord (ψ : E1 → ℂ) x
  calc
    _ = FR ((comp1 ψ).toLp 2 volume) := congrArg FR (pull1_schwartz ψ)
    _ = (𝓕 (comp1 ψ) : 𝓢(ℝ, ℂ)).toLp 2 volume := SchwartzMap.toLp_fourier_eq _
    _ = (comp1 (𝓕 ψ : 𝓢(E1, ℂ))).toLp 2 volume :=
      congrArg (fun s : 𝓢(ℝ, ℂ) => s.toLp 2 volume) hSch
    _ = pull1 ((𝓕 ψ : 𝓢(E1, ℂ)).toLp 2 volume) := (pull1_schwartz _).symm
    _ = _ := congrArg pull1 (SchwartzMap.toLp_fourier_eq ψ).symm

private theorem forward_bounded_real (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (R : ℝ) (hR : 0 ≤ R) (hs : ∀ x : ℝ, R < |x| → g x = 0) :
    ⇑(FR (hg.toLp g)) =ᵐ[volume] (𝓕 g : ℝ → ℂ) := by
  let G : E1 → ℂ := g ∘ coord.symm
  have hG : MemLp G 2 volume := hg.comp_measurePreserving coord.symm.measurePreserving
  have hsG : ∀ ξ : E1, R < ‖ξ‖ → G ξ = 0 := by
    intro ξ hξ
    apply hs
    simpa only [← Real.norm_eq_abs, coord.symm.norm_map] using hξ
  have hforward := forward_bounded_E1 G hG R hR hsG
  have hPull : pull1 (hG.toLp G) = hg.toLp g := by
    apply Lp.ext
    filter_upwards [pull1_coe (hG.toLp G),
      coord.measurePreserving.quasiMeasurePreserving.ae_eq hG.coeFn_toLp,
      hg.coeFn_toLp] with x hp hGx hgx
    calc
      _ = (hG.toLp G) (coord x) := hp
      _ = G (coord x) := hGx
      _ = g x := by simp only [G, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
      _ = _ := hgx.symm
  have hF : FR (hg.toLp g) = pull1 (FE (hG.toLp G)) := by
    rw [← hPull, fourier_pull1]
  rw [hF]
  filter_upwards [pull1_coe (FE (hG.toLp G)),
    coord.measurePreserving.quasiMeasurePreserving.ae_eq hforward] with x hp hfx
  calc
    _ = (FE (hG.toLp G)) (coord x) := hp
    _ = (𝓕 G) (coord x) := by
      simpa only [Function.comp_apply] using hfx <;> rfl
    _ = (𝓕 g) x := by
      have hcomp : G ∘ coord = g := by
        funext y
        simp only [G, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
      exact (Real.fourier_comp_linearIsometry coord G x).symm.trans
        (congrArg (fun z : ℝ → ℂ => (𝓕 z) x) hcomp)
  all_goals rfl

private def negR : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ (E := ℝ)
private def reflect : HR →ₗᵢ[ℂ] HR :=
  Lp.compMeasurePreservingₗᵢ ℂ (negR : ℝ → ℝ) negR.measurePreserving
private def compNeg (ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ negR.toContinuousLinearEquiv ψ

private theorem reflect_coe (f : HR) :
    ⇑(reflect f) =ᵐ[volume] (fun x : ℝ => f (-x)) :=
  Lp.coeFn_compMeasurePreserving f negR.measurePreserving

private theorem reflect_schwartz (ψ : 𝓢(ℝ, ℂ)) :
    reflect (ψ.toLp 2 volume) = (compNeg ψ).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [reflect_coe (ψ.toLp 2 volume),
    negR.measurePreserving.quasiMeasurePreserving.ae_eq (ψ.coeFn_toLp 2 volume),
    (compNeg ψ).coeFn_toLp 2 volume] with x hr hψ hc
  exact hr.trans (hψ.trans hc.symm)

private theorem inverse_reflection (f : HR) : FR.symm f = reflect (FR f) := by
  apply DenseRange.induction_on (p := fun f : HR => FR.symm f = reflect (FR f))
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      (μ := (volume : Measure ℝ)) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq FR.symm.continuous (reflect.continuous.comp FR.continuous)
  intro ψ
  change FR.symm (ψ.toLp 2 volume) = reflect (FR (ψ.toLp 2 volume))
  calc
    _ = (𝓕⁻ ψ : 𝓢(ℝ, ℂ)).toLp 2 volume := SchwartzMap.toLp_fourierInv_eq ψ
    _ = (compNeg (𝓕 ψ : 𝓢(ℝ, ℂ))).toLp 2 volume :=
      congrArg (fun s : 𝓢(ℝ, ℂ) => s.toLp 2 volume) (SchwartzMap.fourierInv_apply_eq ψ)
    _ = reflect ((𝓕 ψ : 𝓢(ℝ, ℂ)).toLp 2 volume) := (reflect_schwartz _).symm
    _ = _ := congrArg reflect (SchwartzMap.toLp_fourier_eq ψ).symm

private theorem inverse_bounded_real (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (R : ℝ) (hR : 0 ≤ R) (hs : ∀ x : ℝ, R < |x| → g x = 0) :
    ⇑(FR.symm (hg.toLp g)) =ᵐ[volume] (𝓕⁻ g : ℝ → ℂ) := by
  rw [inverse_reflection]
  filter_upwards [reflect_coe (FR (hg.toLp g)),
    negR.measurePreserving.quasiMeasurePreserving.ae_eq
      (forward_bounded_real g hg R hR hs)] with x hr hf
  change (reflect (FR (hg.toLp g))) x = (𝓕⁻ g : ℝ → ℂ) x
  calc
    _ = (FR (hg.toLp g)) (-x) := hr
    _ = (𝓕 g : ℝ → ℂ) (-x) := hf
    _ = _ := (Real.fourierInv_eq_fourier_neg g x).symm

/-- Actual same G2 symbol and physical kernel; no assumed Fourier or Ci identity. -/
theorem actual_cutoff_inverse (c N : ℝ) (hc : 0 < c) (hN : c ≤ N) :
    let m := D5.S3.Fourier.Asymptotics.CosineCutoffKernel.symbol c N
    let q := fun x : ℝ =>
      (D5.S3.Fourier.Asymptotics.CosineCutoffKernel.kernel c N x : ℂ)
    ∃ (hm : MemLp m 2 volume) (hq : MemLp q 2 volume),
      ⇑((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hm.toLp m)) =ᵐ[volume] q ∧
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm (hm.toLp m) = hq.toLp q := by
  let m := D5.S3.Fourier.Asymptotics.CosineCutoffKernel.symbol c N
  let q := fun x : ℝ =>
    (D5.S3.Fourier.Asymptotics.CosineCutoffKernel.kernel c N x : ℂ)
  obtain ⟨hMeas, hInt, hm, hBound, hTail, hInv, hZero, hDegenerate⟩ :=
    D5.S3.Fourier.Asymptotics.CosineCutoffKernel.result c N hc hN
  have hN0 : 0 < N := lt_of_lt_of_le hc hN
  have hR : 0 ≤ N / (2 * Real.pi) := by positivity
  have hs : ∀ ξ : ℝ, N / (2 * Real.pi) < |ξ| → m ξ = 0 := by
    intro ξ hξ
    simp only [m, D5.S3.Fourier.Asymptotics.CosineCutoffKernel.symbol,
      not_le.mpr hξ, and_false, if_false]
  have hbridge : ⇑(FR.symm (hm.toLp m)) =ᵐ[volume] q :=
    (inverse_bounded_real m hm _ hR hs).trans (ae_of_all _ hInv)
  have hq : MemLp q 2 volume := (memLp_congr_ae hbridge).mp (Lp.memLp (FR.symm (hm.toLp m)))
  refine ⟨hm, hq, hbridge, ?_⟩
  apply Lp.ext
  exact hbridge.trans hq.coeFn_toLp.symm
end D5.S3.Fourier.Asymptotics.CosineCutoffKernel

noncomputable section
open MeasureTheory FourierTransform Filter
open scoped ENNReal SchwartzMap

namespace D5.S3.Fourier.Asymptotics.CosineCutoffKernel

private abbrev H := Lp ℂ 2 (volume : Measure ℝ)
private abbrev RealH := Lp ℝ 2 (volume : Measure ℝ)

private def mulB : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.lsmul ℂ ℂ
private def pair : H →L[ℂ] H →L[ℂ] ℂ := mulB.lpPairing volume 2 2
private def FL : H →L[ℂ] H := (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
private def IL : H →L[ℂ] H := (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem pair_eq (f g : H) : pair f g = ∫ x, f x * g x := by
  simpa only [pair, mulB, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    (mulB.lpPairing_eq_integral (μ := volume) (p := 2) (q := 2) f g)

set_option maxHeartbeats 1600000 in
/-- The Fourier transform is symmetric for the bilinear L2 pairing. -/
private theorem pair_fourier (a b : H) : pair (𝓕 a) b = pair a (𝓕 b) := by
  let p := fun a : H => pair (𝓕 a) b = pair a (𝓕 b)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      (μ := (volume : Measure ℝ)) ENNReal.ofNat_ne_top) a
  · exact isClosed_eq ((pair.flip b).continuous.comp FL.continuous)
      (pair.flip (𝓕 b)).continuous
  intro ψ
  change pair (𝓕 (ψ.toLp 2 volume)) b = pair (ψ.toLp 2 volume) (𝓕 b)
  rw [SchwartzMap.toLp_fourier_eq, pair_eq, pair_eq]
  have hd := congrArg (fun t : TemperedDistribution ℝ ℂ => t ψ)
    (Lp.fourier_toTemperedDistribution_eq b)
  have ht : (∫ x, (𝓕 ψ) x * b x) = ∫ x, ψ x * (𝓕 b : H) x := by
    simpa only [TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply, smul_eq_mul] using hd
  calc
    (∫ x, ((𝓕 ψ).toLp 2 volume) x * b x) = ∫ x, (𝓕 ψ) x * b x := by
      apply integral_congr_ae
      filter_upwards [(𝓕 ψ).coeFn_toLp 2 volume] with x hx
      rw [hx]
    _ = ∫ x, ψ x * (𝓕 b : H) x := ht
    _ = ∫ x, (ψ.toLp 2 volume) x * (𝓕 b : H) x := by
      apply integral_congr_ae
      filter_upwards [ψ.coeFn_toLp 2 volume] with x hx
      rw [hx]

private theorem product_integrable {a b : ℝ → ℂ}
    (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    Integrable (fun x => a x * b x) volume := by
  exact memLp_one_iff_integrable.mp
    (mulB.memLp_of_bilin 1 ha hb)

private def phase (x ξ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I)

private theorem phase_norm (x ξ : ℝ) : ‖phase x ξ‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem phase_continuous (x : ℝ) : Continuous (phase x) := by
  unfold phase
  fun_prop

private def modulate (x : ℝ) (m : ℝ → ℂ) : ℝ → ℂ := fun ξ => phase x ξ * m ξ

private theorem modulate_memLp (x : ℝ) {m : ℝ → ℂ}
    (hm : MemLp m 2 volume) : MemLp (modulate x m) 2 volume := by
  apply hm.mono ((phase_continuous x).aestronglyMeasurable.mul hm.1)
  filter_upwards with ξ
  simp [modulate, norm_mul, phase_norm]

/-- Pure phase identity; its integrability and L² use are discharged separately. -/
private theorem modulated_row (m : ℝ → ℂ) (x y : ℝ) :
    (𝓕 (modulate x m)) y = (𝓕⁻ m) (x-y) := by
  rw [Real.fourier_eq', Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [modulate, phase, Real.inner_apply, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2 <;> push_cast <;> ring

/-- All inputs are complex ordinary L²; no L¹ premise is placed on f. -/
private theorem convolution_pointwise (m : ℝ → ℂ)
    (hm2 : MemLp m 2 volume)
    (R : ℝ) (hR : 0 ≤ R) (hs : ∀ ξ, R < |ξ| → m ξ = 0) (f : H) (x : ℝ) :
    Integrable (fun y => (𝓕⁻ m) (x-y) * f y) volume ∧
    (∫ y, (𝓕⁻ m) (x-y) * f y) =
      (𝓕⁻ (fun ξ => m ξ * (𝓕 f : H) ξ)) x := by
  let ha := modulate_memLp x hm2
  let A : H := ha.toLp (modulate x m)
  have hrow : (𝓕 A : H) =ᵐ[volume] (fun y => (𝓕⁻ m) (x-y)) :=
    (forward_bounded_real (modulate x m) ha R hR
      (by intro ξ hξ; simp [modulate, hs ξ hξ])).trans
      (ae_of_all _ (modulated_row m x))
  have hr := product_integrable (Lp.memLp (𝓕 A : H)) (Lp.memLp f)
  constructor
  · apply hr.congr
    filter_upwards [hrow] with y hy
    rw [hy]
  · calc
      (∫ y, (𝓕⁻ m) (x-y) * f y) = pair (𝓕 A) f := by
        rw [pair_eq]
        apply integral_congr_ae
        filter_upwards [hrow] with y hy
        rw [hy]
      _ = pair A (𝓕 f) := pair_fourier A f
      _ = ∫ ξ, phase x ξ * (m ξ * (𝓕 f : H) ξ) := by
        rw [pair_eq]
        apply integral_congr_ae
        filter_upwards [ha.coeFn_toLp] with ξ hξ
        rw [hξ]
        simp only [modulate, mul_assoc]
      _ = (𝓕⁻ (fun ξ => m ξ * (𝓕 f : H) ξ)) x := by
        rw [Real.fourierInv_eq']
        simp only [phase, Real.inner_apply, smul_eq_mul, mul_assoc]

private def multiplier (m : ℝ → ℂ) (hm : MemLp m ∞ volume) : H →L[ℂ] H :=
  mulB.holderL volume ∞ 2 2 (hm.toLp m)

private theorem multiplier_ae (m : ℝ → ℂ) (hm : MemLp m ∞ volume) (f : H) :
    (multiplier m hm f : ℝ → ℂ) =ᵐ[volume] (fun ξ => m ξ * f ξ) := by
  have h := mulB.coeFn_holder (r := 2) (hm.toLp m) f
  filter_upwards [h, hm.coeFn_toLp] with ξ hξ hmξ
  simpa only [multiplier, ContinuousLinearMap.holderL_apply_apply,
    mulB, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hmξ] using hξ

private theorem multiplier_bound (m : ℝ → ℂ) (hm : MemLp m ∞ volume)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖m ξ‖ ≤ B) : ‖multiplier m hm‖ ≤ B := by
  apply (multiplier m hm).opNorm_le_bound hB
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplier_ae m hm f] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _)

private def spectralOp (m : ℝ → ℂ) (hm : MemLp m ∞ volume) : H →L[ℂ] H :=
  IL.comp ((multiplier m hm).comp FL)

private theorem spectralOp_bound (m : ℝ → ℂ) (hm : MemLp m ∞ volume)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖m ξ‖ ≤ B) : ‖spectralOp m hm‖ ≤ B := by
  apply (spectralOp m hm).opNorm_le_bound hB
  intro f
  calc
    ‖spectralOp m hm f‖ = ‖multiplier m hm (𝓕 f)‖ :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _
    _ ≤ ‖multiplier m hm‖ * ‖(𝓕 f : H)‖ := (multiplier m hm).le_opNorm _
    _ ≤ B * ‖f‖ := by
      rw [Lp.norm_fourier_eq]
      exact mul_le_mul_of_nonneg_right (multiplier_bound m hm B hB hb) (norm_nonneg _)

/-- Actual ordinary inverse convolution, with its L² output and a.e. representative. -/
private theorem spectralOp_integral (m : ℝ → ℂ)
    (hm2 : MemLp m 2 volume)
    (hmInf : MemLp m ∞ volume) (R : ℝ) (hR : 0 ≤ R)
    (hs : ∀ ξ, R < |ξ| → m ξ = 0) (f : H) :
    (spectralOp m hmInf f : ℝ → ℂ) =ᵐ[volume]
      (fun x => ∫ y, (𝓕⁻ m) (x-y) * f y) := by
  let g : ℝ → ℂ := fun ξ => m ξ * (𝓕 f : H) ξ
  have hg2 : MemLp g 2 volume :=
    MemLp.ae_eq (multiplier_ae m hmInf (𝓕 f))
      (Lp.memLp (multiplier m hmInf (𝓕 f)))
  have hM : multiplier m hmInf (𝓕 f) = hg2.toLp g := by
    apply Lp.ext
    exact (multiplier_ae m hmInf (𝓕 f)).trans hg2.coeFn_toLp.symm
  have hi := inverse_bounded_real g hg2 R hR
    (by intro ξ hξ; simp [g, hs ξ hξ])
  change (𝓕⁻ (multiplier m hmInf (𝓕 f)) : H) =ᵐ[volume] _
  rw [hM]
  exact hi.trans (ae_of_all _ (fun x =>
    (convolution_pointwise m hm2 R hR hs f x).2.symm))


private theorem spectralOp_sub_bound (m n : ℝ → ℂ)
    (hm : MemLp m ∞ volume) (hn : MemLp n ∞ volume)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖m ξ - n ξ‖ ≤ B) :
    ‖spectralOp m hm - spectralOp n hn‖ ≤ B := by
  apply (spectralOp m hm - spectralOp n hn).opNorm_le_bound hB
  intro f
  have hM : ‖multiplier m hm (𝓕 f) - multiplier n hn (𝓕 f)‖ ≤
      B * ‖(𝓕 f : H)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (multiplier m hm (𝓕 f)) (multiplier n hn (𝓕 f)),
      multiplier_ae m hm (𝓕 f), multiplier_ae n hn (𝓕 f)] with ξ hs hmξ hnξ
    rw [hs, Pi.sub_apply, hmξ, hnξ, ← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _)
  calc
    ‖(spectralOp m hm - spectralOp n hn) f‖ =
        ‖multiplier m hm (𝓕 f) - multiplier n hn (𝓕 f)‖ := by
      change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (multiplier m hm (𝓕 f)) -
        (Lp.fourierTransformₗᵢ ℝ ℂ).symm (multiplier n hn (𝓕 f))‖ = _
      rw [← map_sub]
      exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _
    _ ≤ B * ‖(𝓕 f : H)‖ := hM
    _ = B * ‖f‖ := by rw [Lp.norm_fourier_eq]

/-- The actual finite-cutoff convolution on every complex L2 input.
The two toLp equalities identify both the spatial integral and the spectral
product with one bounded operator; the nested estimate uses the actual symbols. -/
theorem actual_cutoff_convolution (c N : ℝ) (hc : 0 < c) (hN : c ≤ N) :
    MemLp (fun x : ℝ => (kernel c N x : ℂ)) 2 volume ∧
    ∃ C : H →L[ℂ] H,
      (∀ (f : H) (x : ℝ), Integrable
        (fun y => (kernel c N (x-y) : ℂ) * f y) volume) ∧
      (∀ f : H,
        ∃ (hg : MemLp (fun ξ => symbol c N ξ * (𝓕 f : H) ξ) 2 volume)
          (hconv : MemLp (fun x => ∫ y, (kernel c N (x-y) : ℂ) * f y) 2 volume),
          (C f : ℝ → ℂ) =ᵐ[volume]
            (fun x => ∫ y, (kernel c N (x-y) : ℂ) * f y) ∧
          C f = hconv.toLp (fun x => ∫ y, (kernel c N (x-y) : ℂ) * f y) ∧
          C f = (Lp.fourierTransformₗᵢ ℝ ℂ).symm
            (hg.toLp (fun ξ => symbol c N ξ * (𝓕 f : H) ξ))) ∧
      ‖C‖ ≤ 2 * Real.pi / c ∧
      (∀ M : ℝ, N ≤ M → ∃ D : H →L[ℂ] H,
        (∀ f : H, (D f : ℝ → ℂ) =ᵐ[volume]
          (fun x => ∫ y, (kernel c M (x-y) : ℂ) * f y)) ∧
        ‖D-C‖ ≤ 2 * Real.pi / N) := by
  classical
  let m : ℝ → ℂ := symbol c N
  obtain ⟨hm, _, hm2, hb, htail, hq, _, _⟩ := result c N hc hN
  obtain ⟨_, hq2, _, _⟩ := actual_cutoff_inverse c N hc hN
  let R : ℝ := N / (2 * Real.pi)
  have hNpos : 0 < N := lt_of_lt_of_le hc hN
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs : ∀ ξ, R < |ξ| → m ξ = 0 := by
    intro ξ hξ
    simp only [m, symbol, show ¬ |ξ| ≤ N/(2*Real.pi) from not_le.mpr hξ,
      and_false, if_false]
  have hmInf : MemLp m ∞ volume := memLp_top_of_bound hm.aestronglyMeasurable
    (2 * Real.pi / c) (ae_of_all _ hb)
  let C : H →L[ℂ] H := spectralOp m hmInf
  have hC (f : H) : (C f : ℝ → ℂ) =ᵐ[volume]
      (fun x => ∫ y, (kernel c N (x-y) : ℂ) * f y) := by
    have h := spectralOp_integral m hm2 hmInf R hR hs f
    simpa only [C, m, hq] using h
  refine ⟨hq2, C, ?_, ?_, spectralOp_bound m hmInf _ (by positivity) hb, ?_⟩
  · intro f x
    simpa only [m, hq] using (convolution_pointwise m hm2 R hR hs f x).1
  · intro f
    let g : ℝ → ℂ := fun ξ => m ξ * (𝓕 f : H) ξ
    have hg : MemLp g 2 volume :=
      MemLp.ae_eq (multiplier_ae m hmInf (𝓕 f))
      (Lp.memLp (multiplier m hmInf (𝓕 f)))
    have hv : multiplier m hmInf (𝓕 f) = hg.toLp g := by
      apply Lp.ext
      exact (multiplier_ae m hmInf (𝓕 f)).trans hg.coeFn_toLp.symm
    have hconv : MemLp (fun x => ∫ y, (kernel c N (x-y) : ℂ) * f y) 2 volume :=
      MemLp.ae_eq (hC f) (Lp.memLp (C f))
    refine ⟨hg, hconv, hC f, ?_, ?_⟩
    · apply Lp.ext
      exact (hC f).trans hconv.coeFn_toLp.symm
    · change (Lp.fourierTransformₗᵢ ℝ ℂ).symm (multiplier m hmInf (𝓕 f)) = _
      rw [hv]
  · intro M hNM
    have hCM : c ≤ M := hN.trans hNM
    obtain ⟨hMm, _, hMm2, hMb, _, hMq, _, _⟩ := result c M hc hCM
    have hMmInf : MemLp (symbol c M) ∞ volume :=
      memLp_top_of_bound hMm.aestronglyMeasurable _ (ae_of_all _ hMb)
    have hMpos : 0 < M := lt_of_lt_of_le hc hCM
    have hRM : 0 ≤ M/(2*Real.pi) := by positivity
    have hsM : ∀ ξ, M/(2*Real.pi) < |ξ| → symbol c M ξ = 0 := by
      intro ξ hξ
      simp only [symbol, not_le.mpr hξ, and_false, if_false]
    refine ⟨spectralOp (symbol c M) hMmInf, ?_, ?_⟩
    · intro f
      simpa only [hMq] using
        (spectralOp_integral (symbol c M) hMm2 hMmInf _ hRM hsM f)
    · exact spectralOp_sub_bound (symbol c M) m hMmInf hmInf _
        (by positivity) (htail M hNM)

/-- Restriction of the actual complex convolution to real L2. -/
private theorem actual_cutoff_real (c N : ℝ) (hc : 0 < c) (hN : c ≤ N) :
    Measurable (kernel c N) ∧ MemLp (kernel c N) 2 volume ∧
    ∃ C : RealH →L[ℝ] RealH,
      (∀ f : RealH, (C f : ℝ → ℝ) =ᵐ[volume]
        (fun x => ∫ y, kernel c N (x-y) * f y)) ∧
      ‖C‖ ≤ 2 * Real.pi / c := by
  obtain ⟨hq2, Cc, hInt, hExact, hn, _⟩ := actual_cutoff_convolution c N hc hN
  have hCc (f : H) : (Cc f : ℝ → ℂ) =ᵐ[volume]
      (fun x => ∫ y, (kernel c N (x-y) : ℂ) * f y) := by
    obtain ⟨_, _, hrep, _, _⟩ := hExact f
    exact hrep
  obtain ⟨_, hm1, _, _, _, hq, _, _⟩ := result c N hc hN
  have hm11 : MemLp (symbol c N) 1 volume := memLp_one_iff_integrable.mpr hm1
  have hci : Continuous (𝓕⁻ (symbol c N) : ℝ → ℂ) := by
    simpa only [Real.Lp.fourierTransformInv_toLp hm11] using
      (Real.Lp.fourierTransformInv (hm11.toLp (symbol c N))).continuous
  have hqc : Continuous (kernel c N) := by
    have h := Complex.continuous_re.comp hci
    convert h using 1
    funext x
    simp only [Function.comp_apply, hq, Complex.ofReal_re]
  have hqreal : MemLp (kernel c N) 2 volume := by
    have h := hq2.re
    change MemLp (fun x => ((kernel c N x : ℂ)).re) 2 volume at h
    simpa only [Complex.ofReal_re] using h
  let J : RealH →L[ℝ] H := Complex.ofRealCLM.compLpL 2 volume
  let ReL : H →L[ℝ] RealH := Complex.reCLM.compLpL 2 volume
  let Cr : RealH →L[ℝ] RealH := ReL.comp ((Cc.restrictScalars ℝ).comp J)
  have hJ (f : RealH) : (J f : ℝ → ℂ) =ᵐ[volume] (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.coeFn_compLpL f
  have hRe (f : H) : (ReL f : ℝ → ℝ) =ᵐ[volume] (fun x => (f x).re) :=
    Complex.reCLM.coeFn_compLpL f
  have hCr (f : RealH) : (Cr f : ℝ → ℝ) =ᵐ[volume]
      (fun x => ∫ y, kernel c N (x-y) * f y) := by
    filter_upwards [hRe (Cc (J f)), hCc (J f)] with x hx hcx
    change (ReL (Cc (J f))) x = _
    rw [hx, hcx]
    change Complex.reCLM (∫ y, (kernel c N (x-y) : ℂ) * (J f) y) = _
    rw [← Complex.reCLM.integral_comp_comm (hInt (J f) x)]
    apply integral_congr_ae
    filter_upwards [hJ f] with y hy
    simp [hy]
  have hCn : ‖Cr‖ ≤ ‖Cc‖ := by
    apply Cr.opNorm_le_bound (norm_nonneg _)
    intro f
    have hre : ‖Cr f‖ ≤ ‖Cc (J f)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hRe (Cc (J f))] with x hx
      change ‖ReL (Cc (J f)) x‖ ≤ _
      rw [hx]
      exact Complex.abs_re_le_norm _
    have hjn : ‖J f‖ ≤ ‖f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hJ f] with x hx
      rw [hx]
      simp
    exact hre.trans ((Cc.le_opNorm (J f)).trans
      (mul_le_mul_of_nonneg_left hjn (norm_nonneg _)))
  exact ⟨hqc.measurable, hqreal, Cr, hCr, hCn.trans hn⟩

end D5.S3.Fourier.Asymptotics.CosineCutoffKernel

namespace D5.S3.Fourier.Asymptotics.CosineCutoffKernel

private theorem weighted_integral_operator (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
    let κ : ℝ := 1/a + α^2/b
    let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
    let μρ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    ∃ T : Lp ℝ 2 (μρ.prod μρ) →L[ℝ] (Lp ℝ 2 μρ →L[ℝ] Lp ℝ 2 μρ),
      (∀ (K : Lp ℝ 2 (μρ.prod μρ)) (f : Lp ℝ 2 μρ),
        (fun x => T K f x) =ᵐ[μρ] (fun x => ∫ y, K (x, y) * f y ∂μρ)) ∧
      (∀ K L, ‖T K - T L‖ ≤ ‖K - L‖) ∧
      (∀ (ι : Type) (l : Filter ι) (Ks : ι → Lp ℝ 2 (μρ.prod μρ))
        (K : Lp ℝ 2 (μρ.prod μρ)), Tendsto Ks l (nhds K) →
        Tendsto (fun i => T (Ks i)) l (nhds (T K))) ∧
      (∀ (K : Lp ℝ 2 (μρ.prod μρ)) (f : Lp ℝ 2 μρ)
        (k : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
        (hk : k =ᵐ[μρ.prod μρ] (K : ℝ × ℝ → ℝ)) (hg : g =ᵐ[μρ] (f : ℝ → ℝ)),
        (∀ᵐ x ∂μρ, Integrable (fun y => k (x,y) * g y) μρ) ∧
        (fun x => ∫ y, k (x,y) * g y ∂μρ) =ᵐ[μρ] (fun x => T K f x)) ∧
      (∀ (ι : Type) (l : Filter ι) (hl : l.NeBot) (Ks : ι → Lp ℝ 2 (μρ.prod μρ))
        (K : Lp ℝ 2 (μρ.prod μρ)) (B : ℝ), Tendsto Ks l (nhds K) →
        (∀ᶠ i in l, ‖T (Ks i)‖ ≤ B) → ‖T K‖ ≤ B) := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
  let κ : ℝ := 1/a + α^2/b
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hκ : 0 < κ := by
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr ha) (div_nonneg (sq_nonneg α) hb.le)
  dsimp only
  let μ : Measure ℝ := volume.withDensity
    (fun x => ENNReal.ofReal (c0 * Real.exp (-κ * x ^ 2 / 2)))
  change ∃ T : Lp ℝ 2 (μ.prod μ) →L[ℝ] (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ), _
  have hsq (X : Type) [MeasurableSpace X] (ν : Measure X) (f : Lp ℝ 2 ν) :
      ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    simp [Real.inner_apply, pow_two]
  have hrow (K : Lp ℝ 2 (μ.prod μ)) :
      ∀ᵐ x ∂μ, MemLp (fun y => K (x,y)) 2 μ := by
    filter_upwards [(Lp.memLp K).aestronglyMeasurable.prodMk_left,
      (Lp.memLp K).integrable_sq.prod_right_ae] with x hm hi
    exact (memLp_two_iff_integrable_sq hm).mpr hi
  have hprod (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      AEStronglyMeasurable (fun z : ℝ × ℝ => K z * f z.2) (μ.prod μ) :=
    (Lp.aestronglyMeasurable K).mul (Lp.aestronglyMeasurable f).comp_snd
  have hbound (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      ∀ᵐ x ∂μ, (∫ y, K (x,y) * f y ∂μ) ^ 2 ≤
        (∫ y, K (x,y) ^ 2 ∂μ) * ‖f‖ ^ 2 := by
    filter_upwards [hrow K] with x hx
    let k := hx.toLp (fun y => K (x,y))
    have hi : (∫ y, K (x,y) * f y ∂μ) = inner ℝ k f := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hx.coeFn_toLp] with y hy
      simp [k, hy, Real.inner_apply, mul_comm]
    have hn : ‖k‖ ^ 2 = ∫ y, K (x,y) ^ 2 ∂μ := by
      rw [hsq ℝ μ k]
      apply integral_congr_ae
      filter_upwards [hx.coeFn_toLp] with y hy
      rw [hy]
    rw [hi, ← hn]
    have hc := norm_inner_le_norm (𝕜 := ℝ) k f
    have hp : 0 ≤ ‖k‖ * ‖f‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hs := mul_self_le_mul_self (norm_nonneg (inner ℝ k f)) hc
    simpa [Real.norm_eq_abs, ← pow_two, sq_abs, mul_pow] using hs
  have hmem (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      MemLp (fun x => ∫ y, K (x,y) * f y ∂μ) 2 μ := by
    have hm := (hprod K f).integral_prod_right'
    apply (memLp_two_iff_integrable_sq hm).mpr
    refine ((Lp.memLp K).integrable_sq.integral_prod_left.mul_const (‖f‖ ^ 2)).mono'
      (hm.pow 2) ?_
    filter_upwards [hbound K f] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (∫ y, K (x,y) * f y ∂μ))] using hx
  let B (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
    (hmem K f).toLp (fun x => ∫ y, K (x,y) * f y ∂μ)
  have hB (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      (B K f : ℝ → ℝ) =ᵐ[μ] (fun x => ∫ y, K (x,y) * f y ∂μ) :=
    (hmem K f).coeFn_toLp
  have hnB (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) : ‖B K f‖ ≤ ‖K‖ * ‖f‖ := by
    have h1 : ‖B K f‖ ^ 2 = ∫ x, (∫ y, K (x,y) * f y ∂μ) ^ 2 ∂μ := by
      rw [hsq ℝ μ (B K f)]
      exact integral_congr_ae ((hB K f).fun_comp (fun z : ℝ => z ^ 2))
    have h2 : ∫ x, (∫ y, K (x,y) ^ 2 ∂μ) * ‖f‖ ^ 2 ∂μ = ‖K‖ ^ 2 * ‖f‖ ^ 2 := by
      rw [integral_mul_const, ← integral_prod (f := fun z : ℝ × ℝ => K z ^ 2)
        (Lp.memLp K).integrable_sq, ← hsq (ℝ × ℝ) (μ.prod μ) K]
    have h3 := integral_mono_ae (hmem K f).integrable_sq
      ((Lp.memLp K).integrable_sq.integral_prod_left.mul_const (‖f‖ ^ 2)) (hbound K f)
    rw [← h1, h2] at h3
    nlinarith [norm_nonneg (B K f), norm_nonneg K, norm_nonneg f,
      mul_nonneg (norm_nonneg K) (norm_nonneg f)]
  have hrowInt (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      ∀ᵐ x ∂μ, Integrable (fun y => K (x,y) * f y) μ := by
    filter_upwards [hrow K] with x hx
    let k := hx.toLp (fun y => K (x,y))
    have hi := L2.integrable_inner (𝕜 := ℝ) k f
    apply hi.congr
    filter_upwards [hx.coeFn_toLp] with y hy
    simp [k, hy, Real.inner_apply, mul_comm]
  have hBaddR (K : Lp ℝ 2 (μ.prod μ)) (f g : Lp ℝ 2 μ) :
      B K (f+g) = B K f + B K g := by
    apply Lp.ext
    filter_upwards [hB K (f+g), hB K f, hB K g, Lp.coeFn_add (B K f) (B K g),
      hrowInt K f, hrowInt K g] with x ha hb hc hd hi hj
    rw [ha, hd]
    simp only [Pi.add_apply]
    rw [hb, hc, ← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy]
    change K (x,y) * (f y + g y) = K (x,y) * f y + K (x,y) * g y
    ring
  have hBsmulR (K : Lp ℝ 2 (μ.prod μ)) (a : ℝ) (f : Lp ℝ 2 μ) :
      B K (a • f) = a • B K f := by
    apply Lp.ext
    filter_upwards [hB K (a • f), hB K f, Lp.coeFn_smul a (B K f)] with x ha hb hc
    rw [ha, hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hb, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul a f] with y hy
    simp only [hy, Pi.smul_apply, smul_eq_mul]
    ring
  have hBaddL (K L : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      B (K+L) f = B K f + B L f := by
    apply Lp.ext
    filter_upwards [hB (K+L) f, hB K f, hB L f, Lp.coeFn_add (B K f) (B L f),
      hrowInt K f, hrowInt L f, Measure.ae_ae_of_ae_prod (Lp.coeFn_add K L)]
      with x ha hb hc hd hi hj he
    rw [ha, hd]
    simp only [Pi.add_apply]
    rw [hb, hc, ← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [he] with y hy
    rw [hy]
    change (K (x,y) + L (x,y)) * f y = K (x,y) * f y + L (x,y) * f y
    ring
  have hBsmulL (a : ℝ) (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      B (a • K) f = a • B K f := by
    apply Lp.ext
    filter_upwards [hB (a • K) f, hB K f, Lp.coeFn_smul a (B K f),
      Measure.ae_ae_of_ae_prod (Lp.coeFn_smul a K)] with x ha hb hc hd
    rw [ha, hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hb, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hd] with y hy
    simp only [hy, Pi.smul_apply, smul_eq_mul]
    ring
  let Bₗ : Lp ℝ 2 (μ.prod μ) →ₗ[ℝ] (Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ) :=
    { toFun := fun K =>
        { toFun := B K
          map_add' := hBaddR K
          map_smul' := fun a f => hBsmulR K a f }
      map_add' := fun K L => by
        apply LinearMap.ext
        intro f
        exact hBaddL K L f
      map_smul' := fun a K => by
        apply LinearMap.ext
        intro f
        exact hBsmulL a K f }
  let T := Bₗ.mkContinuous₂ 1 (by
    intro K f
    change ‖B K f‖ ≤ 1 * ‖K‖ * ‖f‖
    simpa only [one_mul] using hnB K f)
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro K f
    exact hB K f
  · intro K L
    rw [← map_sub T]
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => hnB (K-L) f)
  · intro ι l Ks K hKs
    exact (T.continuous.tendsto K).comp hKs
  · intro K f k g hk hg
    have hke := Measure.ae_ae_of_ae_prod hk
    constructor
    · filter_upwards [hrowInt K f, hke] with x hx he
      apply hx.congr
      filter_upwards [he, hg] with y hy hz
      rw [hy, hz]
    · filter_upwards [hB K f, hke] with x hx he
      change (∫ y, k (x,y) * g y ∂μ) = B K f x
      rw [hx]
      apply integral_congr_ae
      filter_upwards [he, hg] with y hy hz
      rw [hy, hz]
  · intro ι l hl Ks K B hKs hbound
    letI : l.NeBot := hl
    exact le_of_tendsto ((continuous_norm.comp T.continuous).tendsto K |>.comp hKs) hbound


private theorem density_unitary (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
    let κ : ℝ := 1/a + α^2/b
    let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
    let μρ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    ∃ U : Lp ℝ 2 μρ ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ),
      (∀ f, (fun x => U f x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * f x)) ∧
      (∀ h, (fun x => U.symm h x) =ᵐ[μρ] (fun x => h x / Real.sqrt (ρ x))) := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
  let κ : ℝ := 1/a + α^2/b
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hκ : 0 < κ := by
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr ha) (div_nonneg (sq_nonneg α) hb.le)
  dsimp only
  let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
  let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
  change ∃ U : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ), _
  have hρ : ∀ x, 0 < ρ x := fun x => mul_pos hc0 (Real.exp_pos _)
  have hρm : Measurable ρ := by dsimp [ρ]; fun_prop
  have hdm : Measurable (fun x => ENNReal.ofReal (ρ x)) := hρm.ennreal_ofReal
  have hd0 : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (ρ x) ≠ 0 :=
    ae_of_all _ (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (hρ x)))
  have hvol : (volume : Measure ℝ) ≪ μ :=
    withDensity_absolutelyContinuous' hdm.aemeasurable hd0
  have hμ : μ ≪ (volume : Measure ℝ) := withDensity_absolutelyContinuous _ _
  have hs0 : ∀ x, Real.sqrt (ρ x) ≠ 0 := fun x => ne_of_gt (Real.sqrt_pos.mpr (hρ x))
  have hs2 : ∀ x, Real.sqrt (ρ x) ^ 2 = ρ x := fun x => Real.sq_sqrt (hρ x).le
  have hsm : Measurable (fun x => Real.sqrt (ρ x)) := hρm.sqrt
  have hsq (ν : Measure ℝ) (f : Lp ℝ 2 ν) : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    simp [Real.inner_apply, pow_two]
  have hwd (g : ℝ → ℝ) : Integrable g μ ↔ Integrable (fun x => ρ x * g x) volume := by
    have ht := integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
      hdm (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) (g := g)
    simpa [μ, smul_eq_mul, ENNReal.toReal_ofReal (hρ _).le] using ht
  have hwi (g : ℝ → ℝ) : (∫ x, g x ∂μ) = ∫ x, ρ x * g x := by
    have ht := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
      hdm (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) g
    simpa [μ, smul_eq_mul, ENNReal.toReal_ofReal (hρ _).le] using ht
  have hfwd (f : Lp ℝ 2 μ) : MemLp (fun x => Real.sqrt (ρ x) * f x) 2 volume := by
    have hm := hsm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).mono_ac hvol)
    apply (memLp_two_iff_integrable_sq hm).mpr
    have hi := (hwd (fun x => f x ^ 2)).mp (Lp.memLp f).integrable_sq
    have he : (fun x => (Real.sqrt (ρ x) * f x) ^ 2) =
        (fun x => ρ x * f x ^ 2) := by
      funext x
      rw [mul_pow, hs2 x]
    change Integrable (fun x => (Real.sqrt (ρ x) * f x) ^ 2) volume
    rw [he]
    exact hi
  have hbwd (h : Lp ℝ 2 (volume : Measure ℝ)) :
      MemLp (fun x => h x / Real.sqrt (ρ x)) 2 μ := by
    have hm : AEStronglyMeasurable (fun x => h x / Real.sqrt (ρ x)) volume :=
      ((Lp.aestronglyMeasurable h).aemeasurable.div hsm.aemeasurable).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq (hm.mono_ac hμ)).mpr
    apply (hwd (fun x => (h x / Real.sqrt (ρ x)) ^ 2)).mpr
    have he : (fun x => ρ x * (h x / Real.sqrt (ρ x)) ^ 2) =
        (fun x => h x ^ 2) := by
      funext x
      rw [div_pow, hs2 x]
      field_simp [(hρ x).ne']
    rw [he]
    exact (Lp.memLp h).integrable_sq
  let V (f : Lp ℝ 2 μ) : Lp ℝ 2 (volume : Measure ℝ) :=
    (hfwd f).toLp (fun x => Real.sqrt (ρ x) * f x)
  have hV (f : Lp ℝ 2 μ) : (V f : ℝ → ℝ) =ᵐ[volume]
      (fun x => Real.sqrt (ρ x) * f x) := (hfwd f).coeFn_toLp
  have hVa (f g : Lp ℝ 2 μ) : V (f+g) = V f + V g := by
    apply Lp.ext
    filter_upwards [hV (f+g), hV f, hV g, Lp.coeFn_add (V f) (V g),
      hvol.ae_eq (Lp.coeFn_add f g)] with x ha hb hc hd he
    simp only [ha, hd, hb, hc, he, Pi.add_apply, mul_add]
  have hVs (a : ℝ) (f : Lp ℝ 2 μ) : V (a • f) = a • V f := by
    apply Lp.ext
    filter_upwards [hV (a • f), hV f, Lp.coeFn_smul a (V f),
      hvol.ae_eq (Lp.coeFn_smul a f)] with x ha hb hc hd
    simp only [ha, hc, hb, hd, Pi.smul_apply, smul_eq_mul]
    ring
  have hVn (f : Lp ℝ 2 μ) : ‖V f‖ = ‖f‖ := by
    have he : ‖V f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [hsq volume (V f), hsq μ f, hwi]
      apply integral_congr_ae
      filter_upwards [hV f] with x hx
      rw [hx, mul_pow, hs2 x]
    nlinarith [norm_nonneg (V f), norm_nonneg f]
  let Vᵢ : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
    { toFun := V, map_add' := hVa, map_smul' := hVs, norm_map' := hVn }
  have hsurj : Function.Surjective Vᵢ := by
    intro h
    let f := (hbwd h).toLp (fun x => h x / Real.sqrt (ρ x))
    refine ⟨f, ?_⟩
    apply Lp.ext
    filter_upwards [hV f, hvol.ae_eq (hbwd h).coeFn_toLp] with x hx hf
    change V f x = h x
    rw [hx, hf]
    field_simp [hs0 x]
  let U := LinearIsometryEquiv.ofSurjective Vᵢ hsurj
  refine ⟨U, ?_, ?_⟩
  · intro f
    exact hV f
  · intro h
    have hf := hμ.ae_eq (hV (U.symm h))
    filter_upwards [hf] with x hx
    change U.symm h x = h x / Real.sqrt (ρ x)
    have he : V (U.symm h) = h := U.apply_symm_apply h
    rw [he] at hx
    apply (eq_div_iff (hs0 x)).mpr
    simpa [mul_comm] using hx.symm


private theorem gaussian_weighted_kernel (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
    let κ : ℝ := 1/a + α^2/b
    let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ*x^2/2)
    let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    let g0 : ℝ := c0^2 * Real.sqrt (Real.pi/κ)
    (∀ z : ℝ, (∫ x, ρ x * ρ (x-z)) = g0 * Real.exp (-κ*z^2/4)) ∧
    (g0 = ∫ x, ρ x^2) ∧
    (∀ (q : ℝ → ℝ) (hmq : Measurable q) (hq : MemLp q 2 (volume : Measure ℝ)),
      ∃ K : Lp ℝ 2 (μ.prod μ),
        (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q (z.1-z.2)) ∧
        ‖K‖^2 = ∫ z, q z ^ 2 * (g0 * Real.exp (-κ*z^2/4)) ∧
        ‖K‖^2 ≤ g0 * ‖hq.toLp q‖^2) ∧
    (∀ (q p : ℝ → ℝ) (hmq : Measurable q) (hmp : Measurable p)
      (hq : MemLp q 2 (volume : Measure ℝ)) (hp : MemLp p 2 (volume : Measure ℝ))
      (K L : Lp ℝ 2 (μ.prod μ))
      (hK : (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q (z.1-z.2)))
      (hL : (L : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => p (z.1-z.2))),
      ‖K-L‖^2 ≤ g0 * ‖hq.toLp q-hp.toLp p‖^2) ∧
    (∀ (ι : Type) (l : Filter ι) (q : ι → ℝ → ℝ) (p : ℝ → ℝ)
      (hmq : ∀ i, Measurable (q i)) (hmp : Measurable p)
      (hq : ∀ i, MemLp (q i) 2 (volume : Measure ℝ)) (hp : MemLp p 2 (volume : Measure ℝ))
      (Ks : ι → Lp ℝ 2 (μ.prod μ)) (K : Lp ℝ 2 (μ.prod μ))
      (hKs : ∀ i, (Ks i : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q i (z.1-z.2)))
      (hK : (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => p (z.1-z.2))),
      Tendsto (fun i => (hq i).toLp (q i)) l (nhds (hp.toLp p)) → Tendsto Ks l (nhds K)) := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
  let κ : ℝ := 1/a + α^2/b
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hκ : 0 < κ := by
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr ha) (div_nonneg (sq_nonneg α) hb.le)
  let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ*x^2/2)
  have hG : ∀ z : ℝ, (∫ x, ρ x * ρ (x-z)) =
      c0^2 * Real.sqrt (Real.pi/κ) * Real.exp (-κ*z^2/4) := by
    intro z
    have he (x : ℝ) : ρ x * ρ (x-z) =
        (c0^2 * Real.exp (-κ*z^2/4)) * Real.exp (-κ*(x-z/2)^2) := by
      dsimp [ρ]
      have hp : -κ*x^2/2 + -κ*(x-z)^2/2 = -κ*z^2/4 + -κ*(x-z/2)^2 := by ring
      calc
        (c0 * Real.exp (-κ*x^2/2)) * (c0 * Real.exp (-κ*(x-z)^2/2)) =
            c0^2 * Real.exp (-κ*x^2/2 + -κ*(x-z)^2/2) := by rw [Real.exp_add]; ring
        _ = (c0^2 * Real.exp (-κ*z^2/4)) * Real.exp (-κ*(x-z/2)^2) := by
          rw [hp, Real.exp_add]; ring
    calc
      (∫ x, ρ x * ρ (x-z)) = (c0^2 * Real.exp (-κ*z^2/4)) *
          ∫ x : ℝ, Real.exp (-κ*(x-z/2)^2) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ he)
      _ = c0^2 * Real.sqrt (Real.pi/κ) * Real.exp (-κ*z^2/4) := by
        rw [integral_sub_right_eq_self (fun x : ℝ => Real.exp (-κ*x^2)) (z/2),
          integral_gaussian κ]
        ring
  let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
  let g0 : ℝ := c0^2 * Real.sqrt (Real.pi/κ)
  dsimp only
  change (∀ z : ℝ, (∫ x, ρ x * ρ (x-z)) = g0 * Real.exp (-κ*z^2/4)) ∧ _
  have hBuild : ∀ (q : ℝ → ℝ) (hmq : Measurable q) (hq : MemLp q 2 (volume : Measure ℝ)),
      ∃ K : Lp ℝ 2 (μ.prod μ),
        (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q (z.1-z.2)) ∧
        ‖K‖^2 = ∫ z, q z^2 * (g0 * Real.exp (-κ*z^2/4)) ∧
        ‖K‖^2 ≤ g0 * ‖hq.toLp q‖^2 := by
    intro q hmq hq
    have hρ : ∀ x, 0 < ρ x := fun x => mul_pos hc0 (Real.exp_pos _)
    have hρm : Measurable ρ := by dsimp [ρ]; fun_prop
    have hρb (x : ℝ) : ρ x ≤ c0 := by
      have he : -κ*x^2/2 ≤ 0 := by nlinarith [sq_nonneg x]
      dsimp [ρ]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr he) hc0.le
    have hρi : Integrable ρ (volume : Measure ℝ) := by
      have hi : Integrable (fun x : ℝ => Real.exp (-(κ/2)*x^2)) :=
        integrable_exp_neg_mul_sq_iff.mpr (by positivity)
      convert! hi.const_mul c0 using 1
      funext x
      dsimp [ρ]
      congr 2
      ring
    have hq2 := hq.integrable_sq
    let w : ℝ × ℝ → ℝ := fun z => (ρ z.1 * ρ z.2) * q (z.1-z.2)^2
    let v : ℝ × ℝ → ℝ := fun z => (ρ z.1 * ρ (z.1-z.2)) * q z.2^2
    have hwm : Measurable w := by dsimp [w]; fun_prop
    have hvm : Measurable v := by dsimp [v]; fun_prop
    have hw0 (z : ℝ × ℝ) : 0 ≤ w z := by dsimp [w]; positivity
    have hv0 (z : ℝ × ℝ) : 0 ≤ v z := by dsimp [v]; positivity
    have hwr (x : ℝ) : Integrable (fun y => w (x,y)) := by
      have hi := (hq2.comp_sub_left x).const_mul (c0*ρ x)
      refine hi.mono' (hwm.comp measurable_prodMk_left).aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 (x,y))]
      dsimp [w]
      calc
        ρ x * ρ y * q (x-y)^2 ≤ ρ x * c0 * q (x-y)^2 := by gcongr; exact hρb y
        _ = c0 * ρ x * q (x-y)^2 := by ring
    have hwi : Integrable w ((volume : Measure ℝ).prod volume) := by
      apply (integrable_prod_iff hwm.aestronglyMeasurable).mpr
      refine ⟨ae_of_all _ hwr, ?_⟩
      have hi := (hρi.const_mul c0).mul_const (∫ y, q y^2)
      refine hi.mono' (hwm.aestronglyMeasurable.norm.integral_prod_right') ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y => norm_nonneg (w (x,y))))]
      calc
        (∫ y, ‖w (x,y)‖) ≤ ∫ y, c0 * ρ x * q (x-y)^2 := by
          apply integral_mono (hwr x).norm ((hq2.comp_sub_left x).const_mul (c0*ρ x))
          intro y
          change ‖w (x,y)‖ ≤ c0 * ρ x * q (x-y)^2
          rw [Real.norm_eq_abs, abs_of_nonneg (hw0 (x,y))]
          dsimp [w]
          calc
            ρ x * ρ y * q (x-y)^2 ≤ ρ x * c0 * q (x-y)^2 := by gcongr; exact hρb y
            _ = c0 * ρ x * q (x-y)^2 := by ring
        _ = c0 * ρ x * ∫ y, q y^2 := by
          rw [integral_const_mul, integral_sub_left_eq_self (fun y : ℝ => q y^2) volume x]
    have hvi : Integrable v ((volume : Measure ℝ).prod volume) := by
      have hi := (hρi.const_mul c0).mul_prod hq2
      refine hi.mono' hvm.aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hv0 z)]
      dsimp [v]
      calc
        ρ z.1 * ρ (z.1-z.2) * q z.2^2 ≤ ρ z.1 * c0 * q z.2^2 := by
          gcongr
          exact hρb (z.1-z.2)
        _ = c0 * ρ z.1 * q z.2^2 := by ring
    have hprod : μ.prod μ = ((volume : Measure ℝ).prod volume).withDensity
        (fun z => ENNReal.ofReal (ρ z.1 * ρ z.2)) := by
      dsimp [μ]
      rw [prod_withDensity hρm.ennreal_ofReal hρm.ennreal_ofReal]
      congr 1
      funext z
      exact (ENNReal.ofReal_mul (hρ z.1).le).symm
    have hDm : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (ρ z.1 * ρ z.2)) := by fun_prop
    have hDt (z : ℝ × ℝ) : (ENNReal.ofReal (ρ z.1 * ρ z.2)).toReal = ρ z.1 * ρ z.2 :=
      ENNReal.toReal_ofReal (mul_nonneg (hρ z.1).le (hρ z.2).le)
    have hKmem : MemLp (fun z : ℝ × ℝ => q (z.1-z.2)) 2 (μ.prod μ) := by
      have hm : Measurable (fun z : ℝ × ℝ => q (z.1-z.2)) :=
        hmq.comp (measurable_fst.sub measurable_snd)
      apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
      rw [hprod]
      apply (integrable_withDensity_iff_integrable_smul' hDm
        (ae_of_all _ (fun z => ENNReal.ofReal_lt_top))).mpr
      simpa only [hDt, smul_eq_mul] using hwi
    have hshift (x : ℝ) : (∫ y, w (x,y)) = ∫ z, v (x,z) := by
      have he := integral_sub_left_eq_self (fun z : ℝ => v (x,z)) volume x
      simpa only [v, w, sub_sub_cancel] using he
    have hvinner (z : ℝ) : (∫ x, v (x,z)) = q z^2 * (g0 * Real.exp (-κ*z^2/4)) := by
      dsimp [v]
      rw [integral_mul_const, hG z]
      dsimp [g0]
      ring
    have hI : (∫ z, q (z.1-z.2)^2 ∂μ.prod μ) =
        ∫ z, q z^2 * (g0 * Real.exp (-κ*z^2/4)) := by
      have hd := integral_withDensity_eq_integral_toReal_smul
        (μ := (volume : Measure ℝ).prod volume) hDm
        (ae_of_all _ (fun z => ENNReal.ofReal_lt_top))
        (fun z : ℝ × ℝ => q (z.1-z.2)^2)
      rw [hprod]
      calc
        (∫ z, q (z.1-z.2)^2 ∂((volume : Measure ℝ).prod volume).withDensity
            (fun z => ENNReal.ofReal (ρ z.1 * ρ z.2))) = ∫ z, w z ∂volume.prod volume := by
          simpa only [hDt, smul_eq_mul] using hd
        _ = ∫ x, ∫ y, w (x,y) := integral_prod w hwi
        _ = ∫ x, ∫ z, v (x,z) := by simp_rw [hshift]
        _ = ∫ z, ∫ x, v (x,z) := integral_integral_swap hvi
        _ = ∫ z, q z^2 * (g0 * Real.exp (-κ*z^2/4)) := by simp_rw [hvinner]
    let K : Lp ℝ 2 (μ.prod μ) := hKmem.toLp (fun z : ℝ × ℝ => q (z.1-z.2))
    have hsq (X : Type) [MeasurableSpace X] (ν : Measure X) (f : Lp ℝ 2 ν) :
        ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      congr 1
      funext x
      simp [pow_two]
    have hKN : ‖K‖^2 = ∫ z, q z^2 * (g0 * Real.exp (-κ*z^2/4)) := by
      rw [hsq (ℝ × ℝ) (μ.prod μ) K, ← hI]
      exact integral_congr_ae (hKmem.coeFn_toLp.fun_comp (fun a : ℝ => a^2))
    have hQN : ‖hq.toLp q‖^2 = ∫ z, q z^2 := by
      rw [hsq ℝ volume (hq.toLp q)]
      exact integral_congr_ae (hq.coeFn_toLp.fun_comp (fun a : ℝ => a^2))
    refine ⟨K, hKmem.coeFn_toLp, hKN, ?_⟩
    rw [hKN, hQN, ← integral_const_mul]
    apply integral_mono
    · exact hvi.integral_prod_right.congr (ae_of_all _ hvinner)
    · exact hq2.const_mul g0
    · intro z
      have he : Real.exp (-κ*z^2/4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
      have hg0 : 0 ≤ g0 := by dsimp [g0]; positivity
      calc
        q z^2 * (g0 * Real.exp (-κ*z^2/4)) ≤ q z^2 * (g0*1) := by gcongr
        _ = g0 * q z^2 := by ring
  have hPair : ∀ (q p : ℝ → ℝ) (hmq : Measurable q) (hmp : Measurable p)
      (hq : MemLp q 2 (volume : Measure ℝ)) (hp : MemLp p 2 (volume : Measure ℝ))
      (K L : Lp ℝ 2 (μ.prod μ))
      (hK : (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q (z.1-z.2)))
      (hL : (L : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => p (z.1-z.2))),
      ‖K-L‖^2 ≤ g0 * ‖hq.toLp q-hp.toLp p‖^2 := by
    intro q p hmq hmp hq hp K L hK hL
    obtain ⟨D, hD, _, hDn⟩ := hBuild (q-p) (hmq.sub hmp) (hq.sub hp)
    have hKD : K-L = D := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub K L, hK, hL, hD] with z ha hb hc hd
      simp only [ha, Pi.sub_apply, hb, hc, hd]
    have hqp : (hq.sub hp).toLp (q-p) = hq.toLp q-hp.toLp p := by
      apply Lp.ext
      filter_upwards [(hq.sub hp).coeFn_toLp, hq.coeFn_toLp, hp.coeFn_toLp,
        Lp.coeFn_sub (hq.toLp q) (hp.toLp p)] with z ha hb hc hd
      simp only [ha, hd, Pi.sub_apply, hb, hc]
    rw [hKD]
    simpa only [hqp] using hDn
  have hgself : g0 = ∫ x, ρ x^2 := by
    simpa only [g0, sub_zero, pow_two, mul_zero, zero_div, Real.exp_zero, mul_one] using (hG 0).symm
  refine ⟨hG, hgself, hBuild, hPair, ?_⟩
  intro ι l q p hmq hmp hq hp Ks K hKs hK hconv
  have hg0 : 0 ≤ g0 := by dsimp [g0]; positivity
  have hn (i : ι) : ‖Ks i-K‖ ≤ Real.sqrt g0 * ‖(hq i).toLp (q i)-hp.toLp p‖ := by
    have hb := hPair (q i) p (hmq i) hmp (hq i) hp (Ks i) K (hKs i) hK
    have he : (Real.sqrt g0 * ‖(hq i).toLp (q i)-hp.toLp p‖)^2 =
        g0 * ‖(hq i).toLp (q i)-hp.toLp p‖^2 := by
      rw [mul_pow, Real.sq_sqrt hg0]
    nlinarith [norm_nonneg (Ks i-K),
      mul_nonneg (Real.sqrt_nonneg g0) (norm_nonneg ((hq i).toLp (q i)-hp.toLp p))]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun i => norm_nonneg (Ks i-K)) hn
    (by simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hconv)))


private theorem cutoff_conjugacy (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
    let κ : ℝ := 1/a + α^2/b
    let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
    let μρ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    ∀ (q : ℝ → ℝ) (hq : MemLp q 2 (volume : Measure ℝ))
      (C : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ))
      (hC : ∀ h, (fun x => C h x) =ᵐ[volume] (fun x => ∫ y, q (x-y) * h y))
      (T : Lp ℝ 2 μρ →L[ℝ] Lp ℝ 2 μρ)
      (hT : ∀ f, (fun x => T f x) =ᵐ[μρ] (fun x => ∫ y, q (x-y) * f y ∂μρ))
      (U : Lp ℝ 2 μρ ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ))
      (hU : ∀ f, (fun x => U f x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * f x))
      (hUinv : ∀ h, (fun x => U.symm h x) =ᵐ[μρ] (fun x => h x / Real.sqrt (ρ x))),
      ∃ M : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ),
        (∀ h, (fun x => M h x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * h x)) ∧
        ‖M‖ ≤ Real.sqrt c0 ∧
        U.toLinearIsometry.toContinuousLinearMap.comp (T.comp U.symm.toLinearIsometry.toContinuousLinearMap) =
          M.comp (C.comp M) ∧ ‖T‖ ≤ c0 * ‖C‖ := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
  let κ : ℝ := 1/a + α^2/b
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hκ : 0 < κ := by
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr ha) (div_nonneg (sq_nonneg α) hb.le)
  dsimp only
  let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
  let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
  intro q hq C hC T hT U hU hUinv
  have hρ : ∀ x, 0 < ρ x := fun x => mul_pos hc0 (Real.exp_pos _)
  have hρm : Measurable ρ := by dsimp [ρ]; fun_prop
  have hdm : Measurable (fun x => ENNReal.ofReal (ρ x)) := hρm.ennreal_ofReal
  have hd0 : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (ρ x) ≠ 0 :=
    ae_of_all _ (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (hρ x)))
  have hvol : (volume : Measure ℝ) ≪ μ :=
    withDensity_absolutelyContinuous' hdm.aemeasurable hd0
  have hs2 : ∀ x, Real.sqrt (ρ x) ^ 2 = ρ x := fun x => Real.sq_sqrt (hρ x).le
  have hs0 : ∀ x, Real.sqrt (ρ x) ≠ 0 := fun x => ne_of_gt (Real.sqrt_pos.mpr (hρ x))
  have hwi (g : ℝ → ℝ) : (∫ x, g x ∂μ) = ∫ x, ρ x * g x := by
    have ht := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
      hdm (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) g
    simpa [μ, smul_eq_mul, ENNReal.toReal_ofReal (hρ _).le] using ht
  have hρle (x : ℝ) : ρ x ≤ c0 := by
    have he : Real.exp (-κ * x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    exact (mul_le_mul_of_nonneg_left he hc0.le).trans_eq (mul_one c0)
  have hsle (x : ℝ) : Real.sqrt (ρ x) ≤ Real.sqrt c0 := Real.sqrt_le_sqrt (hρle x)
  have hsm : Measurable (fun x => Real.sqrt (ρ x)) := hρm.sqrt
  have hmLp (h : Lp ℝ 2 (volume : Measure ℝ)) :
      MemLp (fun x => Real.sqrt (ρ x) * h x) 2 volume := by
    apply ((Lp.memLp h).const_mul (Real.sqrt c0)).mono
      (hsm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable h))
    filter_upwards with x
    change ‖Real.sqrt (ρ x) * h x‖ ≤ ‖Real.sqrt c0 * h x‖
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hsle x) (abs_nonneg _)
  let V (h : Lp ℝ 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume : Measure ℝ) :=
    (hmLp h).toLp (fun x => Real.sqrt (ρ x) * h x)
  have hV (h : Lp ℝ 2 (volume : Measure ℝ)) :
      (fun x => V h x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * h x) := (hmLp h).coeFn_toLp
  have hVa (h k : Lp ℝ 2 (volume : Measure ℝ)) : V (h+k) = V h + V k := by
    apply Lp.ext
    filter_upwards [hV (h+k), hV h, hV k, Lp.coeFn_add (V h) (V k), Lp.coeFn_add h k]
      with x ha hb hc hd he
    simp only [ha, hd, hb, hc, he, Pi.add_apply, mul_add]
  have hVs (a : ℝ) (h : Lp ℝ 2 (volume : Measure ℝ)) : V (a • h) = a • V h := by
    apply Lp.ext
    filter_upwards [hV (a • h), hV h, Lp.coeFn_smul a (V h), Lp.coeFn_smul a h]
      with x ha hb hc hd
    simp only [ha, hc, hb, hd, Pi.smul_apply, smul_eq_mul]
    ring
  have hVn (h : Lp ℝ 2 (volume : Measure ℝ)) : ‖V h‖ ≤ Real.sqrt c0 * ‖h‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hV h] with x hx
    rw [hx, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hsle x) (norm_nonneg _)
  let Vₗ : Lp ℝ 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
    { toFun := V, map_add' := hVa, map_smul' := hVs }
  let M := Vₗ.mkContinuous (Real.sqrt c0) hVn
  have hM (h : Lp ℝ 2 (volume : Measure ℝ)) :
      (fun x => M h x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * h x) := hV h
  have hMn : ‖M‖ ≤ Real.sqrt c0 :=
    M.opNorm_le_bound (Real.sqrt_nonneg _) hVn
  have hconj : U.toLinearIsometry.toContinuousLinearMap.comp
      (T.comp U.symm.toLinearIsometry.toContinuousLinearMap) = M.comp (C.comp M) := by
    apply ContinuousLinearMap.ext
    intro h
    apply Lp.ext
    change (fun x => U (T (U.symm h)) x) =ᵐ[volume] (fun x => M (C (M h)) x)
    filter_upwards [hU (T (U.symm h)), hvol.ae_eq (hT (U.symm h)),
      hM (C (M h)), hC (M h)] with x hu ht hm hc
    rw [hu, ht, hm, hc]
    congr 1
    rw [hwi]
    apply integral_congr_ae
    filter_upwards [hvol.ae_eq (hUinv h), hM h] with y hi hj
    rw [hi, hj]
    change ρ y * (q (x-y) * (h y / Real.sqrt (ρ y))) =
      q (x-y) * (Real.sqrt (ρ y) * h y)
    have hid : ρ y / Real.sqrt (ρ y) = Real.sqrt (ρ y) := by
      apply (div_eq_iff (hs0 y)).mpr
      simpa only [pow_two] using (hs2 y).symm
    calc
      ρ y * (q (x-y) * (h y / Real.sqrt (ρ y))) =
          q (x-y) * h y * (ρ y / Real.sqrt (ρ y)) := by ring
      _ = q (x-y) * (Real.sqrt (ρ y) * h y) := by rw [hid]; ring
  refine ⟨M, hM, hMn, hconj, ?_⟩
  have hn : ‖U.toLinearIsometry.toContinuousLinearMap.comp
      (T.comp U.symm.toLinearIsometry.toContinuousLinearMap)‖ = ‖T‖ := by
    exact (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp U _).trans
      (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv T U.symm)
  calc
    ‖T‖ = ‖M.comp (C.comp M)‖ := by rw [← hconj, hn]
    _ ≤ ‖M‖ * (‖C‖ * ‖M‖) := (M.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (C.opNorm_comp_le M) (norm_nonneg _))
    _ ≤ Real.sqrt c0 * (‖C‖ * Real.sqrt c0) :=
      mul_le_mul hMn (mul_le_mul_of_nonneg_left hMn (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)
    _ = c0 * ‖C‖ := by
      calc
        Real.sqrt c0 * (‖C‖ * Real.sqrt c0) = (Real.sqrt c0)^2 * ‖C‖ := by ring
        _ = c0 * ‖C‖ := by rw [Real.sq_sqrt hc0.le]


end D5.S3.Fourier.Asymptotics.CosineCutoffKernel

noncomputable section
open MeasureTheory FourierTransform Filter
open scoped ENNReal
namespace D5.S3.Fourier.Asymptotics.CosineCutoffKernel

/-- This theorem constructs T from the actual weighted integral-kernel factory.
Its hypotheses are only the original numerical parameters and cutoff order. -/
theorem actual_weighted_cutoff (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
    let κ : ℝ := 1/a + α^2/b
    let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ*x^2/2)
    let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    ∀ c N : ℝ, 0 < c → c ≤ N →
    ∃ (C : RealH →L[ℝ] RealH)
      (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
      (U : Lp ℝ 2 μ ≃ₗᵢ[ℝ] RealH)
      (M : RealH →L[ℝ] RealH),
      (∀ f : RealH, (C f : ℝ → ℝ) =ᵐ[volume]
        (fun x => ∫ y, kernel c N (x-y) * f y)) ∧
      (∀ f : Lp ℝ 2 μ, (T f : ℝ → ℝ) =ᵐ[μ]
        (fun x => ∫ y, kernel c N (x-y) * f y ∂μ)) ∧
      (∀ f : Lp ℝ 2 μ, ∀ᵐ x ∂μ,
        Integrable (fun y => kernel c N (x-y) * f y) μ) ∧
      (∀ f, (U f : ℝ → ℝ) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * f x)) ∧
      (∀ h, (U.symm h : ℝ → ℝ) =ᵐ[μ] (fun x => h x / Real.sqrt (ρ x))) ∧
      (∀ h, (M h : ℝ → ℝ) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * h x)) ∧
      U.toLinearIsometry.toContinuousLinearMap.comp
        (T.comp U.symm.toLinearIsometry.toContinuousLinearMap) = M.comp (C.comp M) ∧
      ‖C‖ ≤ 2 * Real.pi / c ∧ ‖M‖ ≤ Real.sqrt c0 ∧
      ‖T‖ ≤ c0 * (2 * Real.pi / c) := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
  let κ : ℝ := 1/a + α^2/b
  let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ*x^2/2)
  let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  dsimp only
  intro c N hc hN
  obtain ⟨hmq, hq, C, hC, hCn⟩ := actual_cutoff_real c N hc hN
  obtain ⟨A, hA, hAn, hAlim, hAraw, hAclosed⟩ :=
    weighted_integral_operator r α hr0 hr1
  obtain ⟨U, hU, hUinv⟩ := density_unitary r α hr0 hr1
  obtain ⟨_, _, hBuild, _, _⟩ := gaussian_weighted_kernel r α hr0 hr1
  obtain ⟨K, hK, _, _⟩ := hBuild (kernel c N) hmq hq
  let T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := A K
  have hT (f : Lp ℝ 2 μ) : (T f : ℝ → ℝ) =ᵐ[μ]
      (fun x => ∫ y, kernel c N (x-y) * f y ∂μ) :=
    (hAraw K f (fun z => kernel c N (z.1-z.2)) f hK.symm Filter.EventuallyEq.rfl).2.symm
  have hTi (f : Lp ℝ 2 μ) : ∀ᵐ x ∂μ,
      Integrable (fun y => kernel c N (x-y) * f y) μ :=
    (hAraw K f (fun z => kernel c N (z.1-z.2)) f hK.symm Filter.EventuallyEq.rfl).1
  obtain ⟨M, hM, hMn, hconj, hTn⟩ :=
    cutoff_conjugacy r α hr0 hr1 (kernel c N) hq
      C hC T hT U hU hUinv
  refine ⟨C, T, U, M, hC, hT, hTi, hU, hUinv, hM, hconj, hCn, hMn, ?_⟩
  exact hTn.trans (mul_le_mul_of_nonneg_left hCn hc0.le)


end D5.S3.Fourier.Asymptotics.CosineCutoffKernel
