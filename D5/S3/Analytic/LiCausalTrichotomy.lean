/- GID: D5/S3/Analytic/LiCausalTrichotomy
   generality: I
   mirror-B: D5/B/S3/Analytic/LiCausalTrichotomy
   mirror-E: none(waiver:analytic-proof-only)
   anchors: [gict/theorem/6.13]
   digest: Characterize causal Li tests by integral index and vanishing Cayley monodromy. -/

import D5.S3.Weil.Convention
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace D5.S3.Analytic.LiCausalTrichotomy

open Asymptotics Filter MeasureTheory Set
open D5.S3.Weil.Convention
open scoped ComplexConjugate ENNReal FourierTransform Real Topology
/-- The positive-sign angular Fourier transform used by the Li test. -/
noncomputable def angularFourier (f : ℝ → ℂ) (gamma : ℝ) : ℂ := ∫ u : ℝ, f u * Complex.exp (Complex.I * gamma * u)
/-- The Cayley coordinate whose principal powers are the Li symbols. -/
noncomputable def cayley (gamma : ℝ) : ℂ := (gamma + Complex.I / 2) / (gamma - Complex.I / 2)
/-- The principal-branch Li symbol at a nonnegative real index. -/
noncomputable def liSymbol (kappa gamma : ℝ) : ℂ := cayley gamma ^ (kappa : ℂ) - 1
/-- An `L1` function supported, up to null sets, in the strict past. -/
def IsCausal (f : ℝ → ℂ) : Prop := Integrable f ∧ ∀ᵐ u : ℝ, 0 ≤ u → f u = 0
/-- A causal realization is an actual `L1` inverse representative of the Li symbol. -/
def CausalRealization (kappa : ℝ) : Prop := ∃ f : ℝ → ℂ, IsCausal f ∧ ∀ gamma, angularFourier f gamma = liSymbol kappa gamma
/-- A real index is integral when it is the coercion of a natural number. -/
def IntegralIndex (kappa : ℝ) : Prop := ∃ n : ℕ, kappa = n
/-- Cayley monodromy vanishes when one turn has unit phase. -/
def VanishingMonodromy (kappa : ℝ) : Prop := Complex.exp (2 * Real.pi * Complex.I * kappa) = 1
/-- The standard finite-sum normalization of `L_m^(1)`. -/
noncomputable def laguerreOne (m : ℕ) (x : ℝ) : ℝ := ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * Nat.choose (m + 1) (j + 1) / j.factorial * x ^ j
/-- The one-sided Laguerre packet, with the zero index handled separately. -/
noncomputable def causalPacket (n : ℕ) (u : ℝ) : ℂ := if n = 0 then 0 else if u < 0 then (-(Real.exp (u / 2) * laguerreOne (n - 1) (-u)) : ℝ) else 0
/-- The jump of the principal Li symbol across the Cayley branch cut. -/
noncomputable def branchJump (kappa : ℝ) : ℂ := 2 * Complex.I * Real.sin (Real.pi * kappa)
noncomputable def rightBoundary (kappa : ℝ) : ℂ := Complex.exp (Real.pi * Complex.I * kappa) - 1
noncomputable def leftBoundary (kappa : ℝ) : ℂ := Complex.exp (-Real.pi * Complex.I * kappa) - 1
/-- The classical derivative of the symbol on either side of the cut. -/
noncomputable def symbolDerivative (kappa gamma : ℝ) : ℂ := -Complex.I * kappa * cayley gamma ^ (kappa : ℂ) / (gamma ^ 2 + 1 / 4 : ℝ)
/-- The Fourier remainder produced by integration by parts across the jump. -/
noncomputable def inverseRemainder (kappa u : ℝ) : ℂ := ∫ gamma : ℝ, symbolDerivative kappa gamma * Complex.exp (-Complex.I * gamma * u)
/-- The canonical inverse's off-zero integration-by-parts representative. -/
noncomputable def generalizedInverse (kappa u : ℝ) : ℂ := if u = 0 then 0 else (branchJump kappa + inverseRemainder kappa u) / (2 * Real.pi * Complex.I * u)
theorem positive_kernel_reflects_canonical (gamma u : ℝ) : Complex.exp (Complex.I * gamma * u) = fourierKernel (-gamma) u := by
  simp only [fourierKernel]; congr 1; ring

theorem cayley_ne_zero (gamma : ℝ) : cayley gamma ≠ 0 := by
  rw [cayley, div_ne_zero_iff]
  constructor <;> intro h <;> have := congrArg Complex.im h <;> norm_num at this

@[simp] theorem norm_cayley (gamma : ℝ) : ‖cayley gamma‖ = 1 := by
  have hn : ((gamma : ℂ) - Complex.I / 2) ≠ 0 := by intro h; have := congrArg Complex.im h; norm_num at this
  rw [cayley, norm_div]
  have heq : ‖(gamma : ℂ) + Complex.I / 2‖ = ‖(gamma : ℂ) - Complex.I / 2‖ := by
    rw [Complex.norm_def, Complex.norm_def]; congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.div_re,
      Complex.I_re, zero_mul, zero_div, Complex.add_im, Complex.ofReal_im,
      Complex.I_im, one_mul, Complex.sub_re, Complex.sub_im, zero_sub]
    norm_num
  rw [heq, div_self (norm_ne_zero_iff.mpr hn)]
theorem cayley_im (gamma : ℝ) : (cayley gamma).im = gamma / (gamma ^ 2 + 1 / 4) := by
  simp only [cayley, Complex.div_im, Complex.normSq_apply]; norm_num; ring

theorem continuousAt_cayley (gamma : ℝ) : ContinuousAt cayley gamma := by
  have hnum : ContinuousAt (fun x : ℝ => (x : ℂ) + Complex.I / 2) gamma := by fun_prop
  have hden : ContinuousAt (fun x : ℝ => (x : ℂ) - Complex.I / 2) gamma := by fun_prop
  apply hnum.div hden
  intro h; have := congrArg Complex.im h; norm_num at this
theorem cayley_tendsto_zero : Tendsto cayley (𝓝 0) (𝓝 (-1 : ℂ)) := by
  have hnum : ContinuousAt (fun gamma : ℝ => (gamma : ℂ) + Complex.I / 2) 0 := by fun_prop
  have hden : ContinuousAt (fun gamma : ℝ => (gamma : ℂ) - Complex.I / 2) 0 := by fun_prop
  have h := hnum.div hden (by norm_num : (0 : ℂ) - Complex.I / 2 ≠ 0)
  change Tendsto (fun gamma : ℝ => ((gamma : ℂ) + Complex.I / 2) / (gamma - Complex.I / 2)) (𝓝 0) (𝓝 (-1 : ℂ))
  convert h.tendsto using 1
  · ext gamma; rfl
  · norm_num
@[simp] theorem norm_liSymbol_le (kappa gamma : ℝ) : ‖liSymbol kappa gamma‖ ≤ 2 := by
  rw [liSymbol]; refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_cpow_real, norm_cayley, Real.one_rpow, norm_one]; norm_num

theorem liSymbol_aestronglyMeasurable (kappa : ℝ) : AEStronglyMeasurable (liSymbol kappa) := by
  refine (measurable_of_continuousOn_compl_singleton 0 fun gamma hgamma => ?_).aestronglyMeasurable
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun x => cayley x ^ (kappa : ℂ) - 1) gamma
  apply ContinuousAt.sub
  · exact (continuousAt_cpow_const (b := (kappa : ℂ)) (Or.inr (by rw [cayley_im]; exact div_ne_zero hgamma (by positivity)))).comp (continuousAt_cayley gamma)
  · exact continuousAt_const
noncomputable def scaledLiSymbol (kappa xi : ℝ) : ℂ := liSymbol kappa (-2 * Real.pi * xi)

theorem scaledLiSymbol_memLp (kappa : ℝ) : MemLp (scaledLiSymbol kappa) ∞ := by
  apply memLp_top_of_bound
  · refine (measurable_of_continuousOn_compl_singleton 0 fun xi hxi => ?_).aestronglyMeasurable
    change ContinuousAt (fun x => cayley (-2 * Real.pi * x) ^ (kappa : ℂ) - 1) xi
    apply ContinuousAt.sub
    · exact (continuousAt_cpow_const (b := (kappa : ℂ)) (Or.inr (by rw [cayley_im]; exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hxi) (by positivity)))).comp ((continuousAt_cayley _).comp (by fun_prop))
    · exact continuousAt_const
  · exact 2
  · filter_upwards with xi; exact norm_liSymbol_le kappa (-2 * Real.pi * xi)
noncomputable def scaledSymbolLp (kappa : ℝ) : Lp ℂ ∞ volume := (scaledLiSymbol_memLp kappa).toLp (scaledLiSymbol kappa)
noncomputable def liSymbolDistribution (kappa : ℝ) : 𝓢'(ℝ, ℂ) := (scaledSymbolLp kappa : 𝓢'(ℝ, ℂ))
/-- The canonical generalized inverse in the tempered-distribution sense. -/
noncomputable def generalizedInverseDistribution (kappa : ℝ) : 𝓢'(ℝ, ℂ) := 𝓕⁻ (liSymbolDistribution kappa)
theorem fourier_generalizedInverseDistribution (kappa : ℝ) : 𝓕 (generalizedInverseDistribution kappa) = liSymbolDistribution kappa := by simp [generalizedInverseDistribution]

theorem liSymbolDistribution_apply (kappa : ℝ) (phi : 𝓢(ℝ, ℂ)) :
    liSymbolDistribution kappa phi = ∫ xi : ℝ, phi xi * scaledLiSymbol kappa xi := by
  rw [liSymbolDistribution, MeasureTheory.Lp.toTemperedDistribution_apply]; apply integral_congr_ae
  filter_upwards [(scaledLiSymbol_memLp kappa).coeFn_toLp] with xi hxi
  simp [scaledSymbolLp, hxi, smul_eq_mul]
theorem symbolDerivative_integrable (kappa : ℝ) : Integrable (symbolDerivative kappa) := by
  have hscale : Integrable (fun x : ℝ => (1 + (2 * x) ^ 2)⁻¹) := integrable_inv_one_add_sq.comp_mul_left' (by norm_num)
  refine (hscale.const_mul (4 * |kappa|)).mono' ?_ (ae_of_all _ fun gamma => ?_)
  · refine (measurable_of_continuousOn_compl_singleton 0 fun gamma hgamma => ?_).aestronglyMeasurable
    rw [symbolDerivative]
    apply ContinuousAt.div
    · exact (continuousAt_const.mul_const _).mul ((continuousAt_cpow_const (Or.inr (by rw [cayley_im]; exact div_ne_zero hgamma (by positivity)))).comp (continuousAt_cayley gamma))
    · fun_prop
    · positivity
  · rw [symbolDerivative, norm_div, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Complex.norm_cpow_real, norm_cayley, Real.one_rpow,
      Real.norm_of_nonneg (by positivity)]
    simp only [mul_one, norm_neg, norm_real, Pi.mul_apply]
    have hden : gamma ^ 2 + 1 / 4 ≠ 0 := by positivity
    rw [show 4 * |kappa| * (1 + (2 * gamma) ^ 2)⁻¹ = |kappa| / (gamma ^ 2 + 1 / 4) by field_simp; ring]
theorem inverseRemainder_tendsto (kappa : ℝ) : Tendsto (inverseRemainder kappa) (cocompact ℝ) (𝓝 0) := by
  have heq : inverseRemainder kappa = fun u => 𝓕 (symbolDerivative kappa) (u / (2 * Real.pi)) := by
    funext u
    rw [← angularFourier_eq_fourier (symbolDerivative kappa) (-u)]
    simp only [inverseRemainder, angularFourier]; congr 1; ext gamma; congr 1; ring
  rw [heq]
  exact (Real.zero_at_infty_fourier (symbolDerivative kappa)).comp (Filter.tendsto_cocompact_mul_right₀ (by positivity))
lemma generalizedInverse_isEquivalent_of_tendsto {kappa : ℝ} {l : Filter ℝ}
    (hjump : branchJump kappa ≠ 0) (hrem : Tendsto (inverseRemainder kappa) l (𝓝 0))
    (hu : ∀ᶠ u in l, u ≠ 0) :
    generalizedInverse kappa ~[l] (fun u => ((Real.sin (Real.pi * kappa) / (Real.pi * u) : ℝ) : ℂ)) := by
  have hnum : (fun u => branchJump kappa + inverseRemainder kappa u) ~[l] (fun _ => branchJump kappa) := (isEquivalent_const_iff_tendsto hjump).mpr (tendsto_const_nhds.add hrem)
  have hquot := hnum.div (IsEquivalent.refl : (fun u : ℝ => (2 * Real.pi * Complex.I * u : ℂ)) ~[l] fun u => (2 * Real.pi * Complex.I * u : ℂ))
  apply hquot.congr
  filter_upwards [hu] with u hu
  · simp [generalizedInverse, hu]
  · rw [branchJump]; push_cast; field_simp [Real.pi_ne_zero, hu]; ring
theorem generalizedInverse_tail_pos {kappa : ℝ} (hjump : branchJump kappa ≠ 0) : generalizedInverse kappa ~[atTop] (fun u => ((Real.sin (Real.pi * kappa) / (Real.pi * u) : ℝ) : ℂ)) :=
  generalizedInverse_isEquivalent_of_tendsto hjump ((inverseRemainder_tendsto kappa).mono_left atTop_le_cocompact) (eventually_ne_atTop 0)

theorem generalizedInverse_tail_neg {kappa : ℝ} (hjump : branchJump kappa ≠ 0) : generalizedInverse kappa ~[atBot] (fun u => ((Real.sin (Real.pi * kappa) / (Real.pi * u) : ℝ) : ℂ)) :=
  generalizedInverse_isEquivalent_of_tendsto hjump ((inverseRemainder_tendsto kappa).mono_left atBot_le_cocompact) (eventually_ne_atBot 0)
lemma eventually_ne_of_isEquivalent {l : Filter ℝ} {f g : ℝ → ℂ} (h : f ~[l] g)
    (hg : ∀ᶠ u in l, g u ≠ 0) : ∀ᶠ u in l, f u ≠ 0 := by
  obtain ⟨phi, hphi, heq⟩ := h.exists_eq_mul
  filter_upwards [hphi.eventually_ne one_ne_zero, heq, hg] with u hphi heq hg
  rw [heq]; exact mul_ne_zero hphi hg

theorem cayley_tendsto_right_cut : Tendsto cayley (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within cayley
  · exact cayley_tendsto_zero.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with gamma hgamma
    rw [mem_Ioi] at hgamma; simp only [cayley_im]; exact div_nonneg hgamma.le (by positivity)

theorem cayley_tendsto_left_cut : Tendsto cayley (𝓝[<] 0) (𝓝[{z : ℂ | z.im < 0}] (-1 : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within cayley
  · exact cayley_tendsto_zero.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with gamma hgamma
    rw [mem_Iio] at hgamma; simp only [cayley_im]; exact div_neg_of_neg_of_pos hgamma (by positivity)

theorem liSymbol_tendsto_right (kappa : ℝ) : Tendsto (liSymbol kappa) (𝓝[>] 0) (𝓝 (rightBoundary kappa)) := by
  have hlog := (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := (-1 : ℂ)) (by norm_num) (by norm_num)).comp cayley_tendsto_right_cut
  have hlog' : Tendsto (fun gamma => Complex.log (cayley gamma)) (𝓝[>] 0) (𝓝 (Real.pi * Complex.I)) := by
    convert hlog using 1
    · ext gamma; rfl
    · congr 1; norm_num
  have hexp := Complex.continuous_exp.continuousAt.tendsto.comp (hlog'.mul_const (kappa : ℂ))
  have hfinal := hexp.sub_const 1
  convert hfinal using 1
  · ext gamma; simp [liSymbol, Complex.cpow_def_of_ne_zero (cayley_ne_zero gamma), Function.comp_apply]
  · rfl

theorem liSymbol_tendsto_left (kappa : ℝ) : Tendsto (liSymbol kappa) (𝓝[<] 0) (𝓝 (leftBoundary kappa)) := by
  have hlog := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := (-1 : ℂ)) (by norm_num) (by norm_num)).comp cayley_tendsto_left_cut
  have hlog' : Tendsto (fun gamma => Complex.log (cayley gamma)) (𝓝[<] 0) (𝓝 (-Real.pi * Complex.I)) := by
    convert hlog using 1
    · ext gamma; rfl
    · congr 1; norm_num
  have hexp := Complex.continuous_exp.continuousAt.tendsto.comp (hlog'.mul_const (kappa : ℂ))
  have hfinal := hexp.sub_const 1
  convert hfinal using 1
  · ext gamma; simp [liSymbol, Complex.cpow_def_of_ne_zero (cayley_ne_zero gamma), Function.comp_apply]
  · rfl

theorem boundary_sub_eq_jump (kappa : ℝ) : rightBoundary kappa - leftBoundary kappa = branchJump kappa := by
  rw [rightBoundary, leftBoundary, branchJump]
  have hp : (Real.pi * Complex.I * kappa : ℂ) = (Real.pi * kappa) * Complex.I := by ring
  have hn : (-Real.pi * Complex.I * kappa : ℂ) = -(Real.pi * kappa) * Complex.I := by ring
  rw [hp, hn, Complex.exp_mul_I, Complex.exp_mul_I]; simp; ring

@[simp] theorem liSymbol_zero (gamma : ℝ) : liSymbol 0 gamma = 0 := by simp [liSymbol]

@[simp] theorem causalPacket_zero : causalPacket 0 = 0 := by funext u; simp [causalPacket]

theorem angularFourier_eq_fourier (f : ℝ → ℂ) (gamma : ℝ) :
    angularFourier f gamma = 𝓕 f (-gamma / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  rw [Complex.smul_def]
  congr 1
  · congr 1
    push_cast
    ring
  · exact mul_comm _ _

theorem angularFourier_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (angularFourier f) := by
  rw [show angularFourier f = fun gamma => 𝓕 f (-gamma / (2 * Real.pi)) by
    funext gamma; exact angularFourier_eq_fourier f gamma]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf).comp (by fun_prop)

lemma integrableOn_complex_laplace_moment {a : ℂ} (ha : a.re < 0) (n : ℕ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ n * Complex.exp (a * x)) (Ioi 0) := by
  let r := -a.re
  have hr : 0 < r := neg_pos.mpr ha
  have hgamma : IntegrableOn (fun x : ℝ => Complex.exp (-x) * (x : ℂ) ^ n) (Ioi 0) := by
    convert Complex.GammaIntegral_convergent (s := (n + 1 : ℕ)) (by norm_num) using 1
    ext x; simp [Complex.cpow_natCast]
  have hscaled := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Complex.exp (-x) * (x : ℂ) ^ n) 0 hr).mpr hgamma
  have hmodel : IntegrableOn (fun x : ℝ => Complex.exp (-(r * x)) * (x : ℂ) ^ n) (Ioi 0) := by
    convert hscaled.const_mul ((r : ℂ) ^ n)⁻¹ using 1
    ext x; push_cast; field_simp [hr.ne']; ring
  refine hmodel.congr' (by fun_prop) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  rw [mem_Ioi] at hx
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, Complex.norm_exp]
  congr 2; simp [r]; ring

lemma integral_complex_laplace_moment {a : ℂ} (ha : a.re < 0) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ n * Complex.exp (a * x)) =
      (-1 : ℂ) ^ (n + 1) * n.factorial / a ^ (n + 1) := by
  induction n with
  | zero => simpa using integral_exp_mul_complex_Ioi ha 0
  | succ n ih =>
      have ha0 : a ≠ 0 := fun h => by simp [h] at ha
      have hu (x : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (n + 1)) ((n + 1 : ℕ) * (x : ℂ) ^ n) x := by
        convert (hasDerivAt_pow (n + 1) (x : ℂ)).comp_ofReal using 1 <;> norm_num
      have hv (x : ℝ) : HasDerivAt (fun y : ℝ => Complex.exp (a * y) / a) (Complex.exp (a * x)) x := by
        convert (Complex.hasDerivAt_exp (a * (x : ℂ))).comp x ((hasDerivAt_id (x : ℂ)).const_mul a) |>.comp_ofReal |>.div_const a using 1
        field_simp
      have hzero : Tendsto (fun x : ℝ => (x : ℂ) ^ (n + 1) * (Complex.exp (a * x) / a)) (𝓝[>] 0) (𝓝 0) := by
        convert (continuousAt_ofReal.pow (n + 1)).mul ((Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)).div_const a) |>.tendsto |>.mono_left inf_le_left using 1 <;> simp
      have hinfty : Tendsto (fun x : ℝ => (x : ℂ) ^ (n + 1) * (Complex.exp (a * x) / a)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        convert (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n + 1)).div_const ‖a‖ using 1
        ext x; simp [norm_mul, Complex.norm_exp, div_eq_mul_inv]
      have hip := integral_Ioi_mul_deriv_eq_deriv_mul hu hv (integrableOn_complex_laplace_moment ha (n + 1)) ((integrableOn_complex_laplace_moment ha n).const_mul ((n + 1 : ℕ) / a)) hzero hinfty
      simp only [Pi.mul_apply] at hip
      rw [integral_const_mul, ih] at hip; field_simp [ha0] at hip ⊢
      ring_nf at hip ⊢; simpa [Nat.factorial_succ] using hip

lemma binomial_tail (n : ℕ) (s : ℂ) :
    (∑ j ∈ Finset.range n, (-1 : ℂ) ^ (j + 1) * Nat.choose n (j + 1) /
      s ^ (j + 1)) = (1 - 1 / s) ^ n - 1 := by
  rw [show (1 - 1 / s : ℂ) = -1 / s + 1 by ring, (Commute.all (-1 / s) 1).add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_pow, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    one_mul, add_sub_cancel_left]
  apply Finset.sum_congr rfl; intro j hj; push_cast; ring

theorem cayley_eq_one_sub_inv (gamma : ℝ) : cayley gamma = 1 - 1 / ((1 / 2 : ℂ) + Complex.I * gamma) := by
  rw [cayley]
  have h : (1 / 2 : ℂ) + Complex.I * gamma ≠ 0 := by intro hz; have := congrArg Complex.re hz; norm_num at this
  field_simp [h]; ring

theorem causalPacket_fourier {n : ℕ} (hn : n ≠ 0) (gamma : ℝ) :
    angularFourier (causalPacket n) gamma = liSymbol n gamma := by
  let s : ℂ := 1 / 2 + Complex.I * gamma
  have hsre : (-s).re < 0 := by simp [s]
  rw [angularFourier, causalPacket, if_neg hn]
  change (∫ u : ℝ, (Iio 0).indicator (fun u => (-(Real.exp (u / 2) * laguerreOne (n - 1) (-u)) : ℝ) * Complex.exp (Complex.I * gamma * u)) u) = _
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
  simp only [neg_neg]; rw [laguerreOne]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
    simp_rw [show ∀ j : ℕ, (∫ t : ℝ in Ioi 0, ((t : ℂ) ^ j * Complex.exp (-s * t))) = (-1 : ℂ) ^ (j + 1) * j.factorial / (-s) ^ (j + 1) := fun j => integral_complex_laplace_moment hsre j]
    rw [liSymbol, cayley_eq_one_sub_inv, show (1 / 2 : ℂ) + Complex.I * gamma = s by rfl]
    rw [← binomial_tail n s]; apply Finset.sum_congr
    · simp [hn]
    · intro j hj; push_cast; field_simp; ring
  · intro j hj
    convert (integrableOn_complex_laplace_moment hsre j).const_mul
      ((-1 : ℂ) ^ j * Nat.choose n (j + 1) / j.factorial) using 1
    ext t
    rw [show Complex.exp (-s * t) = (Real.exp (-t / 2) : ℂ) * Complex.exp (-Complex.I * gamma * t) by rw [← Complex.ofReal_exp, ← Complex.exp_add]; congr 1; simp [s]; ring]
    push_cast; ring

theorem causalPacket_isCausal (n : ℕ) : IsCausal (causalPacket n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [IsCausal]
  constructor
  · rw [causalPacket, if_neg hn]
    change Integrable ((Iio 0).indicator (fun u : ℝ => (-(Real.exp (u / 2) * laguerreOne (n - 1) (-u)) : ℝ)))
    rw [integrable_indicator_iff measurableSet_Iio]
    apply ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding).mp
    simp only [preimage_neg_Iio, neg_zero, Function.comp_apply, neg_neg]
    rw [laguerreOne]; simp_rw [Finset.mul_sum]; apply integrable_finsetSum; intro j hj
    convert (integrableOn_complex_laplace_moment (a := (-1 / 2 : ℂ)) (by norm_num) j).const_mul
      (-((-1 : ℝ) ^ j * Nat.choose n (j + 1) / j.factorial) : ℂ) using 1
    ext t
    rw [show Complex.exp ((-1 / 2 : ℂ) * t) = (Real.exp (-t / 2) : ℂ) by rw [← Complex.ofReal_exp]; congr 1; push_cast; ring]
    push_cast; ring
  · filter_upwards with u; intro hu; simp [causalPacket, hn, not_lt.mpr hu]

theorem integralIndex_causal {kappa : ℝ} : IntegralIndex kappa → CausalRealization kappa := by
  rintro ⟨n, rfl⟩; refine ⟨causalPacket n, causalPacket_isCausal n, ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [angularFourier]
  · exact causalPacket_fourier hn

theorem integralIndex_iff_monodromy {kappa : ℝ} (hkappa : 0 ≤ kappa) : IntegralIndex kappa ↔ VanishingMonodromy kappa := by
  rw [IntegralIndex, VanishingMonodromy]; constructor
  · rintro ⟨n, rfl⟩
    rw [show (2 * Real.pi * Complex.I * (n : ℝ) : ℂ) = (n : ℕ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_periodic.nat_mul n
  · intro h
    have him : 0 ≤ (2 * Real.pi * Complex.I * kappa : ℂ).im := by simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; positivity
    obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff_of_im_nonneg him).mp h
    refine ⟨n, ?_⟩; have := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Nat.cast_ofNat] at this
    nlinarith [Real.pi_pos]

theorem integralIndex_iff_sin_eq_zero {kappa : ℝ} (hkappa : 0 ≤ kappa) : IntegralIndex kappa ↔ Real.sin (Real.pi * kappa) = 0 := by
  rw [IntegralIndex, Real.sin_eq_zero_iff]; constructor
  · rintro ⟨n, rfl⟩; exact ⟨n, by norm_num; ring⟩
  · rintro ⟨z, hz⟩
    have hz0 : 0 ≤ z := by have : 0 ≤ (z : ℝ) := by nlinarith [Real.pi_pos]; exact_mod_cast this
    use z.toNat; rw [Int.toNat_of_nonneg hz0]; nlinarith [Real.pi_pos]

theorem nonintegral_jump_ne_zero {kappa : ℝ} (hkappa : 0 ≤ kappa) (hnot : ¬ IntegralIndex kappa) : branchJump kappa ≠ 0 := by
  rw [branchJump, mul_ne_zero_iff]
  exact ⟨mul_ne_zero (by norm_num) Complex.I_ne_zero, mt (integralIndex_iff_sin_eq_zero hkappa).mpr hnot⟩

theorem generalizedInverse_eventually_ne_pos {kappa : ℝ} (hkappa : 0 ≤ kappa) (hnot : ¬ IntegralIndex kappa) : ∀ᶠ u in atTop, generalizedInverse kappa u ≠ 0 := by
  apply eventually_ne_of_isEquivalent (generalizedInverse_tail_pos (nonintegral_jump_ne_zero hkappa hnot))
  filter_upwards [eventually_ne_atTop 0] with u hu
  exact_mod_cast div_ne_zero (mt (integralIndex_iff_sin_eq_zero hkappa).mpr hnot) (mul_ne_zero Real.pi_ne_zero hu)

theorem generalizedInverse_eventually_ne_neg {kappa : ℝ} (hkappa : 0 ≤ kappa) (hnot : ¬ IntegralIndex kappa) : ∀ᶠ u in atBot, generalizedInverse kappa u ≠ 0 := by
  apply eventually_ne_of_isEquivalent (generalizedInverse_tail_neg (nonintegral_jump_ne_zero hkappa hnot))
  filter_upwards [eventually_ne_atBot 0] with u hu
  exact_mod_cast div_ne_zero (mt (integralIndex_iff_sin_eq_zero hkappa).mpr hnot) (mul_ne_zero Real.pi_ne_zero hu)

theorem nonintegral_no_causal_realization {kappa : ℝ} (hkappa : 0 ≤ kappa) (hnot : ¬ IntegralIndex kappa) : ¬ CausalRealization kappa := by
  rintro ⟨f, hf, htransform⟩
  have hc : Continuous (liSymbol kappa) := by rw [← funext htransform]; exact angularFourier_continuous hf.1
  have hr := (liSymbol_tendsto_right kappa).nhds_unique (hc.continuousAt.tendsto.mono_left inf_le_left)
  have hl := (liSymbol_tendsto_left kappa).nhds_unique (hc.continuousAt.tendsto.mono_left inf_le_left)
  apply nonintegral_jump_ne_zero hkappa hnot; rw [← boundary_sub_eq_jump, hr, hl, sub_self]

/-- The complete Li-test trichotomy, including its constructive and nonintegral analytic data. -/
theorem causal_iff_integer_iff_monodromy (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    (CausalRealization kappa ↔ IntegralIndex kappa) ∧
    (IntegralIndex kappa ↔ VanishingMonodromy kappa) ∧
    Tendsto (liSymbol kappa) (𝓝[>] 0) (𝓝 (rightBoundary kappa)) ∧ Tendsto (liSymbol kappa) (𝓝[<] 0) (𝓝 (leftBoundary kappa)) ∧
    rightBoundary kappa - leftBoundary kappa = 2 * Complex.I * Real.sin (Real.pi * kappa) ∧
    liSymbol 0 = 0 ∧ causalPacket 0 = 0 ∧
    (∀ n : ℕ, 1 ≤ n → IsCausal (causalPacket n) ∧ causalPacket n = fun u => if u < 0 then (-(Real.exp (u / 2) * laguerreOne (n - 1) (-u)) : ℝ) else 0 ∧
      ∀ gamma, angularFourier (causalPacket n) gamma = liSymbol n gamma) ∧
    𝓕 (generalizedInverseDistribution kappa) = liSymbolDistribution kappa ∧
    Integrable (symbolDerivative kappa) ∧
    (∀ u ≠ 0, generalizedInverse kappa u = (branchJump kappa + inverseRemainder kappa u) / (2 * Real.pi * Complex.I * u)) ∧
    (¬ IntegralIndex kappa → branchJump kappa ≠ 0 ∧ ¬ CausalRealization kappa ∧
      generalizedInverse kappa ~[atTop] (fun u => ((Real.sin (Real.pi * kappa) / (Real.pi * u) : ℝ) : ℂ)) ∧
      generalizedInverse kappa ~[atBot] (fun u => ((Real.sin (Real.pi * kappa) / (Real.pi * u) : ℝ) : ℂ)) ∧
      (∀ᶠ u in atTop, generalizedInverse kappa u ≠ 0) ∧
      ∀ᶠ u in atBot, generalizedInverse kappa u ≠ 0) := by
  have hcausal : CausalRealization kappa ↔ IntegralIndex kappa := by refine ⟨fun h => Classical.byContradiction fun hn => nonintegral_no_causal_realization hkappa hn h, integralIndex_causal⟩
  refine ⟨hcausal, integralIndex_iff_monodromy hkappa, liSymbol_tendsto_right kappa,
    liSymbol_tendsto_left kappa, ?_, ?_, causalPacket_zero, ?_,
    fourier_generalizedInverseDistribution kappa, symbolDerivative_integrable kappa, ?_, ?_⟩
  · simpa [branchJump] using boundary_sub_eq_jump kappa
  · funext gamma; exact liSymbol_zero gamma
  · intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    refine ⟨causalPacket_isCausal n, ?_, causalPacket_fourier hn0⟩
    funext u; simp [causalPacket, hn0]
  · intro u hu; simp [generalizedInverse, hu]
  · intro hnot
    have hjump := nonintegral_jump_ne_zero hkappa hnot
    exact ⟨hjump, nonintegral_no_causal_realization hkappa hnot,
      generalizedInverse_tail_pos hjump, generalizedInverse_tail_neg hjump,
      generalizedInverse_eventually_ne_pos hkappa hnot,
      generalizedInverse_eventually_ne_neg hkappa hnot⟩

end D5.S3.Analytic.LiCausalTrichotomy
