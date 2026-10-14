/- GID: D5/S3/Fourier/Asymptotics/CosineCutoffKernel
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineCutoffKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The closed finite reciprocal-frequency symbol has the actual cosine cutoff as its ordinary inverse Fourier integral, with logarithmic zero-frequency and null-band endpoint normalization. -/

import D5.S3.Fourier.Asymptotics.CosineCutoffKernel.GaussianWeight
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
def pair : H →L[ℂ] H →L[ℂ] ℂ := mulB.lpPairing volume 2 2
private def FL : H →L[ℂ] H := (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
private def IL : H →L[ℂ] H := (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem pair_eq (f g : H) : pair f g = ∫ x, f x * g x := by
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

theorem product_integrable {a b : ℝ → ℂ}
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
  apply hm.mono ((phase_continuous x).aestronglyMeasurable.mul hm.aestronglyMeasurable)
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
theorem actual_cutoff_real (c N : ℝ) (hc : 0 < c) (hN : c ≤ N) :
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
    GaussianWeight.weighted_integral_operator r α hr0 hr1
  obtain ⟨U, hU, hUinv⟩ := GaussianWeight.density_unitary r α hr0 hr1
  obtain ⟨_, _, hBuild, _, _⟩ := GaussianWeight.gaussian_weighted_kernel r α hr0 hr1
  obtain ⟨K, hK, _, _⟩ := hBuild (kernel c N) hmq hq
  let T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := A K
  have hT (f : Lp ℝ 2 μ) : (T f : ℝ → ℝ) =ᵐ[μ]
      (fun x => ∫ y, kernel c N (x-y) * f y ∂μ) :=
    (hAraw K f (fun z => kernel c N (z.1-z.2)) f hK.symm Filter.EventuallyEq.rfl).2.symm
  have hTi (f : Lp ℝ 2 μ) : ∀ᵐ x ∂μ,
      Integrable (fun y => kernel c N (x-y) * f y) μ :=
    (hAraw K f (fun z => kernel c N (z.1-z.2)) f hK.symm Filter.EventuallyEq.rfl).1
  obtain ⟨M, hM, hMn, hconj, hTn⟩ :=
    GaussianWeight.cutoff_conjugacy r α hr0 hr1 (kernel c N) hq
      C hC T hT U hU hUinv
  refine ⟨C, T, U, M, hC, hT, hTi, hU, hUinv, hM, hconj, hCn, hMn, ?_⟩
  exact hTn.trans (mul_le_mul_of_nonneg_left hCn hc0.le)


end D5.S3.Fourier.Asymptotics.CosineCutoffKernel
