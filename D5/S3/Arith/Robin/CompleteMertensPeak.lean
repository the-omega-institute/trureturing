/- GID: D5/S3/Arith/Robin/CompleteMertensPeak
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/CompleteMertensPeak
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A complete Mertens cumulative peak locates an actual finite Robin violation. -/

import D5.S3.Weil.Mertens.Gamma
import D5.S3.Arith.Robin.QuotientIntegralBudget
import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import D5.S3.Arith.Robin.LcmRobinResponse
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace D5.S3.Arith.Robin.CompleteMertensPeak

open Real Set MeasureTheory Filter Finset
open ArithmeticFunction hiding log
open scoped BigOperators Topology
open D5.S3.Arith.Robin.PrimeFiberPropagation

noncomputable section

/-- The complete Chebyshev error kernel. -/
def psiErrorKernel (u : ℝ) : ℝ := (Chebyshev.psi u - u) / u ^ 2

/-- The unweighted complete Chebyshev tail. -/
def Q (t : ℝ) : ℝ := ∫ u in Ioi t, psiErrorKernel u

/-- The positive logarithmic weight. -/
def r (t : ℝ) : ℝ := QuotientIntegralBudget.weightEnvelope t

/-- The weighted complete Chebyshev tail. -/
def I (t : ℝ) : ℝ := ∫ u in Ioi t, psiErrorKernel u * r u

/-- The finite complete Mangoldt cumulative error. -/
def U (t : ℝ) : ℝ :=
  t * (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
    Chebyshev.psi t - t * log t + (1 + eulerMascheroniConstant) * t

private lemma jy_majorant_integrable {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun u : ℝ =>
      (939 / 100) * (log u) ^ (303 / 200 : ℝ) *
        exp (-(4137 / 5000) * sqrt (log u)) / u) (Ioi t) := by
  let g : ℝ → ℝ := fun v => (939 / 100) * v ^ (303 / 200 : ℝ) *
    exp (-(4137 / 5000) * sqrt v)
  have ht0 : 0 < t := by linarith
  have hlogt : 0 < log t := log_pos (by linarith)
  have hg : IntegrableOn g (Ioi (log t)) := by
    have hbase : IntegrableOn
        (fun v : ℝ => v ^ (303 / 200 : ℝ) *
          exp (-(4137 / 5000) * v ^ (1 / 2 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (303 / 200 : ℝ)) (p := (1 / 2 : ℝ)) (b := (4137 / 5000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    have h : IntegrableOn
        (fun v : ℝ => (939 / 100) * (v ^ (303 / 200 : ℝ) *
          exp (-(4137 / 5000) * v ^ (1 / 2 : ℝ)))) (Ioi 0) :=
      hbase.const_mul (939 / 100 : ℝ)
    have hm := h.mono_set (Ioi_subset_Ioi hlogt.le)
    simpa only [g, sqrt_eq_rpow, mul_assoc] using hm
  have hmajor : IntegrableOn (fun u : ℝ => u⁻¹ * g (log u)) (Ioi t) := by
    simpa only [smul_eq_mul] using (integrableOn_comp_log_Ioi g ht0).mpr hg
  convert hmajor using 1
  ext u
  dsimp [g]
  ring

private lemma kernel_integrable
    (hJY : ∀ u : ℝ, 2 ≤ u → |Chebyshev.psi u - u| ≤
      (939 / 100) * u * (log u) ^ (303 / 200 : ℝ) *
        exp (-(4137 / 5000) * sqrt (log u)))
    {t : ℝ} (ht : 2 ≤ t) : IntegrableOn psiErrorKernel (Ioi t) := by
  apply (jy_majorant_integrable ht).mono'
    ((Chebyshev.psi_mono.measurable.sub measurable_id).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change t < u at hu
  have hu2 : 2 ≤ u := ht.trans hu.le
  have hu0 : 0 < u := by linarith
  change |(Chebyshev.psi u - u) / u ^ 2| ≤ _
  rw [abs_div, abs_of_nonneg (sq_nonneg u)]
  calc
    |Chebyshev.psi u - u| / u ^ 2 ≤
        ((939 / 100) * u * (log u) ^ (303 / 200 : ℝ) *
          exp (-(4137 / 5000) * sqrt (log u))) / u ^ 2 :=
      div_le_div_of_nonneg_right (hJY u hu2) (sq_nonneg u)
    _ = (939 / 100) * (log u) ^ (303 / 200 : ℝ) *
        exp (-(4137 / 5000) * sqrt (log u)) / u := by
      field_simp [hu0.ne'] <;> ring

private lemma inv_log_pow_integrable {t : ℝ} (ht : 2 ≤ t)
    (hf : IntegrableOn psiErrorKernel (Ioi t)) (k : ℕ) :
    IntegrableOn (fun u => psiErrorKernel u / (log u) ^ k) (Ioi t) := by
  have hl : 0 < log t := log_pos (by linarith)
  have hbound : ∀ᵐ u : ℝ ∂volume.restrict (Ioi t),
      ‖1 / (log u) ^ k‖ ≤ 1 / (log t) ^ k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change t < u at hu
    have hlu : log t ≤ log u := log_le_log (by linarith) hu.le
    have hlu0 : 0 < log u := hl.trans_le hlu
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (log u) ^ k)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl.le hlu k)
  change Integrable (fun u => psiErrorKernel u / (log u) ^ k) (volume.restrict (Ioi t))
  simpa only [div_eq_mul_inv, one_mul] using
    hf.mul_bdd (g := fun u => 1 / (log u) ^ k)
      ((measurable_const.div (Real.measurable_log.pow_const k)).aestronglyMeasurable) hbound

private lemma weighted_kernel_integrable {t : ℝ} (ht : 2 ≤ t)
    (hf : IntegrableOn psiErrorKernel (Ioi t)) :
    IntegrableOn (fun u => psiErrorKernel u * r u) (Ioi t) := by
  have hlog1 : IntegrableOn (fun u => psiErrorKernel u / log u) (Ioi t) := by
    simpa only [pow_one] using inv_log_pow_integrable ht hf 1
  apply ((inv_log_pow_integrable ht hf 2).add hlog1).congr_fun _ measurableSet_Ioi
  intro u hu
  change t < u at hu
  have hlu : log u ≠ 0 := ne_of_gt (log_pos (by linarith [hu] : 1 < u))
  dsimp [r, QuotientIntegralBudget.weightEnvelope]
  field_simp [hlu] <;> ring

private def triangle (s u : ℝ) : ℝ :=
  {p : ℝ × ℝ | p.1 < p.2}.indicator
    (fun p => (1 / (p.1 * log p.1 ^ 2)) * psiErrorKernel p.2) (s, u)

private lemma triangle_integrable {t : ℝ} (ht : 2 ≤ t)
    (hf : IntegrableOn psiErrorKernel (Ioi t)) :
    Integrable (Function.uncurry triangle)
      ((volume.restrict (Ioi t)).prod (volume.restrict (Ioi t))) := by
  exact ((Mertens.integrable_const_div_mul_log_sq (1 : ℝ) ht).mul_prod hf).indicator
    (measurableSet_lt measurable_fst measurable_snd)

private lemma triangle_right {t s : ℝ} (hs : t < s) :
    (∫ u in Ioi t, triangle s u) = Q s / (s * log s ^ 2) := by
  have heq : (fun u => triangle s u) =
      (Ioi s).indicator (fun u => (1 / (s * log s ^ 2)) * psiErrorKernel u) := by
    ext u
    simp only [triangle, indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioi]
  rw [heq, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hs.le), integral_const_mul]
  dsimp [Q]
  ring

private lemma triangle_left {t u : ℝ} (ht : 2 ≤ t) (hu : t < u) :
    (∫ s in Ioi t, triangle s u) =
      psiErrorKernel u * (1 / log t - 1 / log u) := by
  have heq : (fun s => triangle s u) =
      (Iio u).indicator (fun s => (1 / (s * log s ^ 2)) * psiErrorKernel u) := by
    ext s
    simp only [triangle, indicator_apply, Set.mem_ofPred_eq, Set.mem_Iio]
  rw [heq, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Ioi_inter_Iio,
    integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hu.le]
  have hdiff := intervalIntegral.integral_Ioi_sub_Ioi
    (Mertens.integrable_const_div_mul_log_sq (1 : ℝ) ht) hu.le
  rw [Mertens.integ_div_mul_log_sq 1 ht,
    Mertens.integ_div_mul_log_sq 1 (ht.trans hu.le)] at hdiff
  rw [← hdiff]
  ring

private lemma tail_log_integral {t : ℝ} (ht : 2 ≤ t)
    (hf : IntegrableOn psiErrorKernel (Ioi t)) :
    IntegrableOn (fun s => Q s / (s * log s ^ 2)) (Ioi t) ∧
      (∫ s in Ioi t, Q s / (s * log s ^ 2)) =
        Q t / log t - ∫ u in Ioi t, psiErrorKernel u / log u := by
  have htri := triangle_integrable ht hf
  have hint : IntegrableOn (fun s => Q s / (s * log s ^ 2)) (Ioi t) := by
    apply htri.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact triangle_right hs
  refine ⟨hint, ?_⟩
  have hswap := integral_integral_swap htri
  have hfirst : (∫ s in Ioi t, ∫ u in Ioi t, triangle s u) =
      ∫ s in Ioi t, Q s / (s * log s ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact triangle_right hs
  have hsecond : (∫ u in Ioi t, ∫ s in Ioi t, triangle s u) =
      ∫ u in Ioi t, psiErrorKernel u * (1 / log t - 1 / log u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact triangle_left ht hu
  rw [hfirst, hsecond] at hswap
  rw [hswap]
  have hlog := inv_log_pow_integrable ht hf 1
  simp only [pow_one] at hlog
  have heq : (fun u => psiErrorKernel u * (1 / log t - 1 / log u)) =
      (fun u => psiErrorKernel u / log t - psiErrorKernel u / log u) := by
    ext u; ring
  rw [heq, integral_sub (hf.div_const _) hlog, integral_div]
  rfl

/-- Johnston--Yang decay and Lay's complete identity give the weighted Mertens ledger. -/
private theorem complete_mertens_ledger
    (hJY : ∀ u : ℝ, 2 ≤ u → |Chebyshev.psi u - u| ≤
      (939 / 100) * u * (log u) ^ (303 / 200 : ℝ) *
        exp (-(4137 / 5000) * sqrt (log u)))
    (hLay : ∀ t : ℝ, 2 ≤ t → Q t = Chebyshev.psi t / t -
      (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
        log t - 1 - eulerMascheroniConstant)
    {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn psiErrorKernel (Ioi t) ∧
      IntegrableOn (fun u => psiErrorKernel u * r u) (Ioi t) ∧
        Mertens.E₂Λ t = (Chebyshev.psi t - t) / (t * log t) - I t := by
  have hf := kernel_integrable hJY ht
  refine ⟨hf, weighted_kernel_integrable ht hf, ?_⟩
  have hlog1 : IntegrableOn (fun u => psiErrorKernel u / log u) (Ioi t) := by
    simpa only [pow_one] using inv_log_pow_integrable ht hf 1
  have hlog2 := inv_log_pow_integrable ht hf 2
  obtain ⟨hQint, hQ⟩ := tail_log_integral ht hf
  have hE (u : ℝ) (hu : 2 ≤ u) :
      Mertens.E₁Λ u = (Chebyshev.psi u - u) / u -
        eulerMascheroniConstant - Q u := by
    have hu0 : u ≠ 0 := ne_of_gt (by linarith)
    have h := hLay u hu
    dsimp [Mertens.E₁Λ]
    field_simp [hu0] at h ⊢
    linarith
  have hintegrand : ∀ u ∈ Ioi t,
      Mertens.E₁Λ u / (u * log u ^ 2) =
        psiErrorKernel u / log u ^ 2 -
          eulerMascheroniConstant / (u * log u ^ 2) - Q u / (u * log u ^ 2) := by
    intro u hu
    change t < u at hu
    rw [hE u (ht.trans hu.le)]
    dsimp [psiErrorKernel]
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu])
    have hlu : log u ≠ 0 := ne_of_gt (log_pos (by linarith [hu] : 1 < u))
    field_simp [hu0, hlu] <;> ring
  have hEi : (∫ u in Ioi t, Mertens.E₁Λ u / (u * log u ^ 2)) =
      (∫ u in Ioi t, psiErrorKernel u / log u ^ 2) -
        eulerMascheroniConstant / log t -
          (Q t / log t - ∫ u in Ioi t, psiErrorKernel u / log u) := by
    have hc : IntegrableOn
        (fun u : ℝ => eulerMascheroniConstant / (u * log u ^ 2)) (Ioi t) :=
      Mertens.integrable_const_div_mul_log_sq eulerMascheroniConstant ht
    dsimp only [IntegrableOn] at hlog2 hc hQint
    have hsplit := integral_sub
      (f := fun u => psiErrorKernel u / log u ^ 2 -
        eulerMascheroniConstant / (u * log u ^ 2))
      (g := fun u => Q u / (u * log u ^ 2)) (hlog2.sub hc) hQint
    rw [setIntegral_congr_fun measurableSet_Ioi hintegrand,
      hsplit, integral_sub hlog2 hc,
      Mertens.integ_div_mul_log_sq _ ht, hQ]
  have hI : I t = (∫ u in Ioi t, psiErrorKernel u / log u ^ 2) +
      ∫ u in Ioi t, psiErrorKernel u / log u := by
    dsimp [I]
    rw [← integral_add hlog2 hlog1]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change t < u at hu
    dsimp [r, QuotientIntegralBudget.weightEnvelope]
    have hlu : log u ≠ 0 := ne_of_gt (log_pos (by linarith [hu] : 1 < u))
    field_simp [hlu] <;> ring
  rw [Mertens.E₂Λ.eq ht, hEi, hE t ht, hI]
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt : log t ≠ 0 := ne_of_gt (log_pos (by linarith : 1 < t))
  field_simp [ht0, hlt] <;> ring


private def w (t : ℝ) : ℝ :=
  Real.log t * (Real.log t + 2) / (t * (1 + Real.log t) ^ 2)

private lemma r_pos {t : ℝ} (ht : 1 < t) : 0 < r t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl0 : log t ≠ 0 := ne_of_gt (log_pos ht)
  have heq : r t = t ^ 2 * MellinWeightedVariation.weight t := by
    dsimp [r, QuotientIntegralBudget.weightEnvelope, MellinWeightedVariation.weight]
    field_simp [ht0, hl0] <;> ring
  rw [heq]
  exact mul_pos (sq_pos_of_ne_zero ht0) (OriginalMovingWindowMoment.weight_pos ht)

private lemma r_antitone {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : r t ≤ r s := by
  have ht0 : 0 < t := by linarith
  have h := QuotientIntegralBudget.weight_le hs hst
  have heq : MellinWeightedVariation.weight t = r t / t ^ 2 := by
    dsimp [MellinWeightedVariation.weight, r, QuotientIntegralBudget.weightEnvelope]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at h
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos ht0)).mp h

private lemma reciprocal_r_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u => 1 / r u) (w t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl := Real.log_pos ht
  have hl1 : 1 + Real.log t ≠ 0 := by positivity
  have h := ((Real.hasDerivAt_log ht0).pow 2).div
    ((Real.hasDerivAt_log ht0).const_add 1) hl1
  have heq : (fun u : ℝ => 1 / r u) =
      (fun u => (Real.log u) ^ 2 / (1 + Real.log u)) := by
    funext u
    simp only [r, QuotientIntegralBudget.weightEnvelope, one_div_div]
  rw [heq]
  convert h using 1 <;> dsimp [w] <;> field_simp [ht0, hl1] <;> ring

private lemma w_bounds {t : ℝ} (ht : 1 < t) : 0 ≤ w t ∧ w t ≤ 1 / t := by
  have ht0 : 0 < t := by linarith
  have hl := Real.log_pos ht
  have hden : 0 < t * (1 + Real.log t) ^ 2 := by positivity
  constructor
  · unfold w
    positivity
  · unfold w
    apply (div_le_div_iff₀ hden ht0).2
    nlinarith

private lemma finite_kernel_change {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hf : IntegrableOn psiErrorKernel (Ioi a))
    (hfr : IntegrableOn (fun u => psiErrorKernel u * r u) (Ioi a)) :
    IntervalIntegrable (fun t => w t * I t) volume a b ∧
      Q a = I a / r a + (∫ t in a..b, w t * I t) + Q b - I b / r b := by
  let F : ℝ → ℝ := fun x => I a - ∫ u in a..x, psiErrorKernel u * r u
  let H : ℝ → ℝ := fun x => 1 / r x
  have hf' : IntegrableOn psiErrorKernel (Ioi b) :=
    hf.mono_set (Ioi_subset_Ioi hab)
  have hfi : IntervalIntegrable (fun u => psiErrorKernel u * r u) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hfr.mono_set Ioc_subset_Ioi_self
  have hF : ∀ x ∈ Icc a b, F x = I x := by
    intro x hx
    have hsplit := intervalIntegral.integral_interval_add_Ioi hfr
      (hfr.mono_set (Ioi_subset_Ioi hx.1))
    change (∫ u in a..x, psiErrorKernel u * r u) + I x = I a at hsplit
    dsimp [F]
    linarith
  have hFac : AbsolutelyContinuousOnInterval F a b := by
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => I a) a b :=
      ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
    exact hc.sub (hfi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp))
  have hHac : AbsolutelyContinuousOnInterval H a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := ne_of_gt (by linarith)
    have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have hl1 : 1 + Real.log t ≠ 0 := by linarith [Real.log_pos ht1]
    have hr0 : (1 + Real.log t) / (Real.log t) ^ 2 ≠ 0 :=
      div_ne_zero hl1 (pow_ne_zero 2 hl0)
    dsimp [H, r, QuotientIntegralBudget.weightEnvelope]
    simp only [one_div_div]
    fun_prop (disch := assumption)
  have hFTC := hFac.integral_deriv_mul_eq_sub hHac
  have hderiv : ∀ᵐ t, t ∈ uIoc a b →
      deriv F t * H t + F t * deriv H t =
        -psiErrorKernel t + w t * I t := by
    filter_upwards [hfi.ae_hasDerivAt_integral] with t ht htab
    have htcc : t ∈ uIcc a b := uIoc_subset_uIcc htab
    have htIcc : t ∈ Icc a b := by simpa [uIcc_of_le hab] using htcc
    have ht1 : 1 < t := by linarith [htIcc.1]
    have hFd : deriv F t = -(psiErrorKernel t * r t) := by
      exact ((ht htcc a (by simp)).const_sub (I a)).deriv
    have hHd : deriv H t = w t := (reciprocal_r_hasDerivAt ht1).deriv
    rw [hFd, hHd, hF t htIcc]
    dsimp [H]
    field_simp [ne_of_gt (r_pos ht1)] <;> ring
  rw [intervalIntegral.integral_congr_ae hderiv] at hFTC
  have hwi : IntervalIntegrable (fun t => w t * I t) volume a b := by
    have hh := hHac.intervalIntegrable_deriv.mul_continuousOn hFac.continuousOn
    apply hh.congr
    intro t ht
    have htIcc : t ∈ Icc a b := by simpa [uIcc_of_le hab] using uIoc_subset_uIcc ht
    change deriv H t * F t = w t * I t
    rw [hF t htIcc]
    exact congrArg (fun z => z * I t)
      (reciprocal_r_hasDerivAt (by linarith [htIcc.1])).deriv
  have hpi : IntervalIntegrable psiErrorKernel volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hf.mono_set Ioc_subset_Ioi_self
  rw [intervalIntegral.integral_add
      (f := fun t => -psiErrorKernel t) (g := fun t => w t * I t) hpi.neg hwi,
    intervalIntegral.integral_neg, hF b ⟨hab, le_rfl⟩, hF a ⟨le_rfl, hab⟩] at hFTC
  have hQ := intervalIntegral.integral_interval_add_Ioi hf hf'
  change (∫ u in a..b, psiErrorKernel u) + Q b = Q a at hQ
  dsimp [H] at hFTC
  refine ⟨hwi, ?_⟩
  simp only [div_eq_mul_inv, one_mul] at hFTC ⊢
  linarith only [hFTC, hQ]

private lemma tail_difference_bound {x : ℝ} (hx : 2 ≤ x)
    (hf : IntegrableOn psiErrorKernel (Ioi x))
    (hfr : IntegrableOn (fun u => psiErrorKernel u * r u) (Ioi x)) :
    |Q x - I x / r x| ≤ 2 * ∫ u in Ioi x, |psiErrorKernel u| := by
  have hrx := r_pos (by linarith : 1 < x)
  have hI : |I x| ≤ r x * ∫ u in Ioi x, |psiErrorKernel u| := by
    calc
      |I x| ≤ ∫ u in Ioi x, |psiErrorKernel u * r u| := abs_integral_le_integral_abs
      _ ≤ ∫ u in Ioi x, r x * |psiErrorKernel u| := by
        apply setIntegral_mono_on hfr.abs (hf.abs.const_mul _) measurableSet_Ioi
        intro u hu
        change x < u at hu
        rw [abs_mul, abs_of_pos (r_pos (by linarith [hu] : 1 < u))]
        have hr := r_antitone (show 1 < x by linarith) hu.le
        nlinarith [abs_nonneg (psiErrorKernel u)]
      _ = r x * ∫ u in Ioi x, |psiErrorKernel u| := integral_const_mul _ _
  have hdiv : |I x / r x| ≤ ∫ u in Ioi x, |psiErrorKernel u| := by
    rw [abs_div, abs_of_pos hrx]
    exact (div_le_iff₀ hrx).2 (by nlinarith [hI])
  have hQ : |Q x| ≤ ∫ u in Ioi x, |psiErrorKernel u| := abs_integral_le_integral_abs
  exact (abs_sub _ _).trans (by linarith)

private theorem complete_mangoldt_le_neg_E3 {x : ℝ} (hx : 2 ≤ x) :
    Mertens.E₂Λ x ≤ -Mertens.E₃ x := by
  let K : ℕ := ⌊Real.log x / Real.log 2⌋₊
  have hx1 : 1 ≤ x := by linarith
  have hsum :
      (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt d / ((d : ℝ) * Real.log d)) ≤
      ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
        -Real.log (1 - 1 / (p : ℝ)) := by
    simp_rw [vonMangoldt_apply, ite_div, zero_div, ← Finset.sum_filter,
      Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith : 0 ≤ x)]
    calc
      _ = ∑ k ∈ Finset.Icc 1 K,
          ∑ p ∈ (Finset.Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
            (1 : ℝ) / ((k : ℝ) * (p : ℝ) ^ k) := by
        refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun p hp => ?_
        have hk0 : k ≠ 0 := by
          have := (Finset.mem_Icc.mp hk).1
          omega
        have hpp : p.Prime := (Finset.mem_filter.mp hp).2
        have hkp : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
        have hpp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
        have hlog : Real.log (p : ℝ) ≠ 0 :=
          (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
        rw [Nat.Prime.pow_minFac hpp hk0]
        simp only [Nat.cast_pow, Real.log_pow]
        field_simp [hlog, hkp, hpp0]
        <;> ring
      _ ≤ ∑ k ∈ Finset.Icc 1 K,
          ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
            (1 : ℝ) / ((k : ℝ) * (p : ℝ) ^ k) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : (1 : ℝ) ≤ k := by
          exact_mod_cast (Finset.mem_Icc.mp hk).1
        have hroot : x ^ (1 / (k : ℝ)) ≤ x :=
          Real.rpow_le_self_of_one_le hx1
            ((div_le_one₀ (by linarith : 0 < (k : ℝ))).mpr hk1)
        have hsub : (Finset.Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime ⊆
            (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
          intro p hp
          obtain ⟨hpi, hpp⟩ := Finset.mem_filter.mp hp
          obtain ⟨hp0, hpx⟩ := Finset.mem_Ioc.mp hpi
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_Ioc.mpr ⟨hp0, hpx.trans (Nat.floor_mono hroot)⟩, hpp⟩
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro p hp hnot
          positivity)
      _ = ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
          ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / ((k : ℝ) * (p : ℝ) ^ k) :=
        Finset.sum_comm
      _ ≤ _ := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpp : p.Prime := (Finset.mem_filter.mp hp).2
        have hseries :
            HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) * (p : ℝ) ^ k))
              (-Real.log (1 - 1 / (p : ℝ))) := by
          apply (hasSum_nat_add_iff' 1).mp
          simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_div,
            sub_zero, Nat.cast_add, Nat.cast_one, neg_div, neg_neg, div_zero, sub_zero] using
            (Mertens.HasSum_log_one_sub_one_div_prime hpp).neg
        exact sum_le_hasSum (Finset.Icc 1 K) (by
          intro k hk
          positivity) hseries
  simp only [Finset.sum_neg_distrib] at hsum
  unfold Mertens.E₂Λ Mertens.E₃
  rw [Mertens.γ.eq_eulerMascheroni]
  linarith
private lemma fifth_moment_tail {z : ℝ} (hz : 16 ≤ z) :
    IntegrableOn (fun v : ℝ => v ^ 5 * exp (-(4 / 5) * v)) (Ioi z) ∧
      (∫ v in Ioi z, v ^ 5 * exp (-(4 / 5) * v)) ≤
        (5 / 2) * z ^ 5 * exp (-(4 / 5) * z) := by
  let P : ℝ → ℝ := fun v => -(5 / 2) * v ^ 5 * exp (-(4 / 5) * v)
  let d : ℝ → ℝ := fun v => v ^ 4 * (2 * v - 25 / 2) * exp (-(4 / 5) * v)
  have hd (v : ℝ) : HasDerivAt P (d v) v := by
    have he := ((hasDerivAt_id v).const_mul (-(4 / 5 : ℝ))).exp
    have hh := ((hasDerivAt_pow 5 v).const_mul (-(5 / 2 : ℝ))).mul he
    change HasDerivAt (fun u : ℝ => (-(5 / 2 : ℝ) * u ^ 5) *
      exp (-(4 / 5) * u)) _ v at hh
    convert hh using 1 <;> dsimp [P, d] <;> ring
  have hlim : Tendsto P atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      5 (4 / 5) (by norm_num)).const_mul (-(5 / 2 : ℝ))
    simpa [P, Real.rpow_ofNat, mul_assoc] using h
  have hdpos (v : ℝ) (hv : v ∈ Ioi z) : 0 ≤ d v := by
    change z < v at hv
    dsimp [d]
    apply mul_nonneg _ (exp_pos _).le
    exact mul_nonneg (pow_nonneg (by linarith [hv] : 0 ≤ v) 4) (by linarith [hv])
  have hdi : IntegrableOn d (Ioi z) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun v _ => hd v) hdpos hlim
  have hpoint (v : ℝ) (hv : v ∈ Ioi z) :
      v ^ 5 * exp (-(4 / 5) * v) ≤ d v := by
    change z < v at hv
    have h := mul_le_mul_of_nonneg_left
      (show v ≤ 2 * v - 25 / 2 by linarith [hv])
      (show 0 ≤ v ^ 4 * exp (-(4 / 5) * v) by positivity)
    dsimp [d]
    nlinarith [h]
  have hi : IntegrableOn (fun v : ℝ => v ^ 5 * exp (-(4 / 5) * v)) (Ioi z) := by
    apply hdi.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change z < v at hv
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have : 0 ≤ v := by linarith [hv]
      positivity : 0 ≤ v ^ 5 * exp (-(4 / 5) * v))]
    exact hpoint v hv
  refine ⟨hi, (setIntegral_mono_on hi hdi measurableSet_Ioi hpoint).trans_eq ?_⟩
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun v _ => hd v) hdi hlim
  simpa [P] using heq

private lemma jy_tail_bound
    (hJY : ∀ u : ℝ, 2 ≤ u → |Chebyshev.psi u - u| ≤
      (939 / 100) * u * (Real.log u) ^ (303 / 200 : ℝ) *
        Real.exp (-(4137 / 5000) * Real.sqrt (Real.log u)))
    {x : ℝ} (hx : 2 ≤ x) (hz : 16 ≤ sqrt (log x))
    (hf : IntegrableOn psiErrorKernel (Ioi x)) :
    (∫ u in Ioi x, |psiErrorKernel u|) ≤
      50 * (sqrt (log x)) ^ 5 * exp (-(4 / 5) * sqrt (log x)) := by
  let c : ℝ := 4137 / 5000
  let g : ℝ → ℝ := fun v => (939 / 100) * v ^ (303 / 200 : ℝ) * exp (-c * sqrt v)
  let z := sqrt (log x)
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hzi := (fifth_moment_tail hz).1
  have hsub : (∫ u in Ioi x, g (log u) / u) = ∫ v in Ioi (log x), g v := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using integral_comp_log_Ioi g hx0
  have hsub₂ : (∫ v in Ioi (log x), g v) =
      ∫ v in Ioi z, 2 * v * g (v ^ 2) := by
    have h := integral_comp_rpow_Ioi_of_pos'
      (g := g) (p := (2 : ℝ)) (by norm_num) hlx.le
    simpa only [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow, Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, smul_eq_mul, z] using h.symm
  have hmajor : IntegrableOn (fun u : ℝ => g (log u) / u) (Ioi x) := by
    simpa only [g, c] using jy_majorant_integrable hx
  have hfirst : (∫ u in Ioi x, |psiErrorKernel u|) ≤
      ∫ u in Ioi x, g (log u) / u := by
    apply setIntegral_mono_on hf.abs hmajor measurableSet_Ioi
    intro u hu
    have hu2 : 2 ≤ u := hx.trans hu.le
    have hu0 : 0 < u := by linarith
    rw [psiErrorKernel, abs_div, abs_of_nonneg (sq_nonneg u)]
    have h := div_le_div_of_nonneg_right (hJY u hu2) (sq_nonneg u)
    convert h using 1 <;> dsimp [g, c] <;> field_simp <;> ring
  have hpoint : ∀ v ∈ Ioi z, 2 * v * g (v ^ 2) ≤
      (939 / 50) * (v ^ 5 * exp (-(4 / 5) * v)) := by
    intro v hv
    change z < v at hv
    have hv1 : 1 ≤ v := by linarith
    have hv0 : 0 < v := by linarith
    have hp : v ^ (303 / 100 : ℝ) ≤ v ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
    have he : exp (-c * v) ≤ exp (-(4 / 5) * v) := by
      apply exp_le_exp.mpr
      dsimp [c]
      nlinarith
    have hs : sqrt (v ^ 2) = v := sqrt_sq hv0.le
    have hr : (v ^ 2) ^ (303 / 200 : ℝ) = v ^ (303 / 100 : ℝ) := by
      rw [← Real.rpow_natCast v 2, ← Real.rpow_mul hv0.le]
      norm_num
    dsimp [g]
    rw [hs, hr]
    have hprod := mul_le_mul hp he (exp_pos _).le (by positivity)
    rw [Real.rpow_ofNat] at hprod
    have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (939 / 50 : ℝ) * v by positivity)
    nlinarith [h]
  have htrans : IntegrableOn (fun v : ℝ => 2 * v * g (v ^ 2)) (Ioi z) := by
    apply (hzi.const_mul (939 / 50 : ℝ)).mono' (by dsimp [g]; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change z < v at hv
    have hv0 : 0 ≤ v := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; positivity)]
    exact hpoint v hv
  calc
    _ ≤ ∫ u in Ioi x, g (log u) / u := hfirst
    _ = ∫ v in Ioi z, 2 * v * g (v ^ 2) := hsub.trans hsub₂
    _ ≤ ∫ v in Ioi z, (939 / 50) * (v ^ 5 * exp (-(4 / 5) * v)) :=
      setIntegral_mono_on htrans (hzi.const_mul _) measurableSet_Ioi hpoint
    _ = (939 / 50) * ∫ v in Ioi z, v ^ 5 * exp (-(4 / 5) * v) := integral_const_mul _ _
    _ ≤ (939 / 50) * ((5 / 2) * z ^ 5 * exp (-(4 / 5) * z)) :=
      mul_le_mul_of_nonneg_left (fifth_moment_tail hz).2 (by norm_num)
    _ ≤ 50 * (sqrt (log x)) ^ 5 * exp (-(4 / 5) * sqrt (log x)) := by
      dsimp [z]
      nlinarith [mul_nonneg (pow_nonneg (sqrt_nonneg (log x)) 5)
        (exp_pos (-(4 / 5) * sqrt (log x))).le]

private lemma far_tail_small {A : ℝ} (hA : 10000 ≤ A) :
    let B := exp (4 * (log A + 20) ^ 2)
    100 * (sqrt (log B)) ^ 5 * exp (-(4 / 5) * sqrt (log B)) < 1 / (2 * sqrt A) := by
  let L := log A
  have hA0 : 0 < A := by linarith
  have hL : 0 ≤ L := log_nonneg (by linarith)
  have hAroot : 0 < sqrt A := sqrt_pos.2 hA0
  have hz : sqrt (log (exp (4 * (log A + 20) ^ 2))) = 2 * (L + 20) := by
    rw [log_exp, show 4 * (log A + 20) ^ 2 = (2 * (L + 20)) ^ 2 by dsimp [L]; ring]
    exact sqrt_sq (by linarith)
  dsimp only
  rw [hz]
  let z := 2 * (L + 20)
  have hz0 : 0 < z := by dsimp [z]; linarith
  have hlog40 : log (40 : ℝ) < 4 := by
    have heq : log (40 : ℝ) = 3 * log 2 + log 5 := by
      rw [show (40 : ℝ) = 2 ^ 3 * 5 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
      norm_num
    rw [heq]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlog200 : log (200 : ℝ) < 6 := by
    have heq : log (200 : ℝ) = 3 * log 2 + 2 * log 5 := by
      rw [show (200 : ℝ) = 2 ^ 3 * 5 ^ 2 by norm_num,
        log_mul (by norm_num) (by norm_num), log_pow, log_pow]
      norm_num
    rw [heq]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlogz : log z ≤ log 40 + L / 20 := by
    have hp : 0 < 1 + L / 20 := by positivity
    have heq : z = 40 * (1 + L / 20) := by dsimp [z]; ring
    rw [heq, log_mul (by norm_num) hp.ne']
    have h := log_le_sub_one_of_pos hp
    linarith
  let V := 200 * sqrt A * z ^ 5 * exp (-(4 / 5) * z)
  have hV0 : 0 < V := by dsimp [V]; positivity
  have hlogV : log V < 0 := by
    have heq : log V = log 200 + L / 2 + 5 * log z - (4 / 5) * z := by
      dsimp [V]
      rw [log_mul (by positivity) (exp_ne_zero _), log_exp,
        log_mul (by positivity) (by positivity), log_pow,
        log_mul (by norm_num) hAroot.ne', log_sqrt hA0.le]
      dsimp [L]
      ring
    rw [heq]
    dsimp [z]
    linarith
  have hV : V < 1 := by
    have h := (Real.log_lt_iff_lt_exp hV0).mp hlogV
    simpa using h
  apply (lt_div_iff₀ (by positivity : 0 < 2 * sqrt A)).2
  dsimp [V, z] at hV ⊢
  nlinarith

private lemma finite_lower_bound {a b : ℝ} (ha : 10000 ≤ a) (hab : a ≤ b)
    (hi : IntervalIntegrable (fun t => w t * I t) volume a b)
    (hI : ∀ t ∈ Icc a b, -4 / sqrt t ≤ I t) :
    -8 / sqrt a ≤ ∫ t in a..b, w t * I t := by
  have ha0 : 0 < a := by linarith
  have hp : ∀ t ∈ uIcc a b, 0 < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hk : IntervalIntegrable (fun t : ℝ => 1 / (t * sqrt t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 := hp t ht
    have hs0 := sqrt_pos.2 ht0
    fun_prop (disch := positivity)
  have heval : (∫ t in a..b, 1 / (t * sqrt t)) = -2 / sqrt b - -2 / sqrt a := by
    have hb0 : 0 < b := ha0.trans_le hab
    have hzero : (0 : ℝ) ∉ uIcc a b := by
      rw [uIcc_of_le hab]
      simp only [Set.mem_Icc, not_and]
      intro h
      linarith
    have heq := integral_rpow (a := a) (b := b) (r := (-3 / 2 : ℝ))
      (Or.inr ⟨by norm_num, hzero⟩)
    have hkernel : ∀ t ∈ uIcc a b, 1 / (t * sqrt t) = t ^ (-3 / 2 : ℝ) := by
      intro t ht
      rw [show (-3 / 2 : ℝ) = -(1 + 1 / 2) by norm_num,
        Real.rpow_neg (hp t ht).le, Real.rpow_add (hp t ht), Real.rpow_one,
        ← Real.sqrt_eq_rpow, one_div]
    rw [intervalIntegral.integral_congr hkernel, heq,
      show (-3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num,
      Real.rpow_neg ha0.le, Real.rpow_neg hb0.le, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow]
    ring
  have hmono : (∫ t in a..b, -4 * (1 / (t * sqrt t))) ≤
      ∫ t in a..b, w t * I t := by
    apply intervalIntegral.integral_mono_on hab (hk.const_mul _) hi
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hs := sqrt_pos.2 (show 0 < t by linarith)
    have hw := w_bounds ht1
    have hdiv := div_le_div_of_nonneg_right hw.2 hs.le
    have hprod := mul_le_mul_of_nonneg_left (hI t ht) hw.1
    have heq : (1 / t) / sqrt t = 1 / (t * sqrt t) := by ring
    rw [heq] at hdiv
    simp only [div_eq_mul_inv] at hdiv hprod ⊢
    nlinarith only [hdiv, hprod]
  rw [intervalIntegral.integral_const_mul, heval] at hmono
  have hsb : 0 ≤ 2 / sqrt b := by positivity
  simp only [div_eq_mul_inv] at hmono hsb ⊢
  linarith only [hmono, hsb]

theorem complete_mertens_peak
    (hJY : ∀ u : ℝ, 2 ≤ u → |Chebyshev.psi u - u| ≤
      (939 / 100) * u * (Real.log u) ^ (303 / 200 : ℝ) *
        Real.exp (-(4137 / 5000) * Real.sqrt (Real.log u)))
    (hLay : ∀ t : ℝ, 2 ≤ t → Q t = Chebyshev.psi t / t -
      (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
        Real.log t - 1 - Real.eulerMascheroniConstant)
    {A : ℝ} (hA : 10000 ≤ A)
    (hpeak : Real.sqrt A * (4 * (Real.log A) ^ 2 / (1 + Real.log A) + 9) < U A) :
    ∃ t ∈ Set.Icc A (Real.exp (4 * (Real.log A + 20) ^ 2)),
      let N := Nat.lcmUpto ⌊t⌋₊
      5040 < N ∧ (N : ℝ) ≤ Real.exp
        (Real.exp (4 * (Real.log A + 20) ^ 2) *
          Real.log (Real.exp (4 * (Real.log A + 20) ^ 2))) ∧
        divisorRatio N > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N) := by
  let B := exp (4 * (log A + 20) ^ 2)
  have hA2 : 2 ≤ A := by linarith
  have hA0 : 0 < A := by linarith
  have hlogA : 0 ≤ log A := log_nonneg (by linarith)
  have hsA : 0 < sqrt A := sqrt_pos.2 hA0
  have hAB : A ≤ B := by
    rw [← exp_log hA0]
    apply exp_le_exp.mpr
    nlinarith [sq_nonneg (log A)]
  have hB2 : 2 ≤ B := hA2.trans hAB
  have hz : sqrt (log B) = 2 * (log A + 20) := by
    dsimp [B]
    rw [log_exp, show 4 * (log A + 20) ^ 2 = (2 * (log A + 20)) ^ 2 by ring]
    exact sqrt_sq (by linarith)
  have hz16 : 16 ≤ sqrt (log B) := by rw [hz]; linarith
  have hledger (t : ℝ) (ht : 2 ≤ t) := complete_mertens_ledger hJY hLay ht
  have hex : ∃ t ∈ Icc A B, Mertens.E₃ t <
      -4 / sqrt t - (Chebyshev.psi t - t) / (t * log t) := by
    by_contra hnone
    have hI : ∀ t ∈ Icc A B, -4 / sqrt t ≤ I t := by
      intro t ht
      have ht2 : 2 ≤ t := hA2.trans ht.1
      have hE : -4 / sqrt t - (Chebyshev.psi t - t) / (t * log t) ≤ Mertens.E₃ t := by
        apply not_lt.mp
        intro h
        exact hnone ⟨t, ht, h⟩
      have hcmp := complete_mangoldt_le_neg_E3 ht2
      rw [(hledger t ht2).2.2] at hcmp
      linarith
    have hAf := hledger A hA2
    have hBf := hledger B hB2
    have hchange := finite_kernel_change hA2 hAB hAf.1 hAf.2.1
    have hfinite := finite_lower_bound hA hAB hchange.1 hI
    have hfirst := div_le_div_of_nonneg_right (hI A ⟨le_rfl, hAB⟩)
      (r_pos (show 1 < A by linarith)).le
    have htail : |Q B - I B / r B| < 1 / (2 * sqrt A) := by
      calc
        _ ≤ 2 * ∫ u in Ioi B, |psiErrorKernel u| :=
          tail_difference_bound hB2 hBf.1 hBf.2.1
        _ ≤ 2 * (50 * (sqrt (log B)) ^ 5 * exp (-(4 / 5) * sqrt (log B))) :=
          mul_le_mul_of_nonneg_left (jy_tail_bound hJY hB2 hz16 hBf.1) (by norm_num)
        _ = 100 * (sqrt (log B)) ^ 5 * exp (-(4 / 5) * sqrt (log B)) := by ring
        _ < 1 / (2 * sqrt A) := far_tail_small hA
    have htailLower := (abs_lt.mp htail).1
    have hQlow : -(4 / r A + 17 / 2) / sqrt A < Q A := by
      have heq : (-4 / sqrt A) / r A - 8 / sqrt A - 1 / (2 * sqrt A) =
          -(4 / r A + 17 / 2) / sqrt A := by ring
      rw [← heq]
      have hchg := hchange.2
      simp only [div_eq_mul_inv] at hfirst hfinite htailLower hchg ⊢
      linarith only [hfirst, hfinite, htailLower, hchg]
    have hU : U A = -A * Q A := by
      unfold U
      rw [hLay A hA2]
      field_simp [hA0.ne']
      ring
    have hr : 4 / r A = 4 * (log A) ^ 2 / (1 + log A) := by
      simp only [r, QuotientIntegralBudget.weightEnvelope, div_div_eq_mul_div]
    have hpeak' : sqrt A * (4 / r A + 9) < -A * Q A := by
      rw [hr, ← hU]
      exact hpeak
    have hp : 4 / r A + 9 < -sqrt A * Q A := by
      have hmul : -A * Q A = sqrt A * (-sqrt A * Q A) := by
        calc
          -A * Q A = -(sqrt A * sqrt A) * Q A := by
            rw [Real.mul_self_sqrt hA0.le]
          _ = sqrt A * (-sqrt A * Q A) := by ring
      have hh : sqrt A * (4 / r A + 9) < sqrt A * (-sqrt A * Q A) := by
        exact hmul ▸ hpeak'
      exact (mul_lt_mul_iff_right₀ hsA).mp hh
    have hq := (div_lt_iff₀ hsA).mp hQlow
    nlinarith
  obtain ⟨t, ht, hE⟩ := hex
  have ht10000 : 10000 ≤ t := hA.trans ht.1
  have hresponse := LcmRobinResponse.common_robin_response ht10000 hE
  have ht0 : 0 < t := by linarith
  have hB0 : 0 ≤ B := (hA0.le.trans hAB)
  have hlogt : 0 ≤ log t := log_nonneg (by linarith)
  have hscale : t * log t ≤ B * log B :=
    mul_le_mul ht.2 (log_le_log ht0 ht.2) hlogt hB0
  refine ⟨t, ht, ?_⟩
  dsimp only
  exact ⟨hresponse.2.1, hresponse.2.2.2.trans (exp_le_exp.mpr hscale), hresponse.1⟩

end
end D5.S3.Arith.Robin.CompleteMertensPeak
