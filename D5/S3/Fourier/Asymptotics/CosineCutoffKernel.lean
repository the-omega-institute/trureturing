/- GID: D5/S3/Fourier/Asymptotics/CosineCutoffKernel
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineCutoffKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The closed finite reciprocal-frequency symbol has the actual cosine cutoff as its ordinary inverse Fourier integral, with logarithmic zero-frequency and null-band endpoint normalization. -/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic
open MeasureTheory Set
open scoped FourierTransform
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

end D5.S3.Fourier.Asymptotics.CosineCutoffKernel
