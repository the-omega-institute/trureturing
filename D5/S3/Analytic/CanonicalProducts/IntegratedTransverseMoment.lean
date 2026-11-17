/- GID: D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment
   generality: G
   mirror-B: D5/B/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrated logarithmic defects recover the extended weighted transverse second moment. -/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory
open scoped Topology BigOperators ENNReal

noncomputable section
namespace D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment

def logKernel (a gamma t : ℝ) : ℝ :=
  Real.log ((t - a)^2 + gamma^2) + Real.log ((t + a)^2 + gamma^2) -
    2 * Real.log (t^2 + gamma^2)

def endpointKernel (a gamma T : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..a, Real.log (((T + v)^2 + gamma^2) / ((T - v)^2 + gamma^2))

def defect {I : Type*} (w a gamma : I → ℝ) (t : ℝ) : ℝ :=
  ∑' i, w i * logKernel (a i) (gamma i) t

def integratedDefect {I : Type*} (w a gamma : I → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, defect w a gamma t



private def qlog (g x : ℝ) : ℝ := Real.log (x^2 + g^2)
private def qprime (g x : ℝ) : ℝ := 2 * x / (x^2 + g^2)
private def edge (g T v : ℝ) : ℝ := qlog g (T + v) - qlog g (T - v)

private lemma qpos {g : ℝ} (hg : 0 < g) (x : ℝ) : 0 < x^2 + g^2 := by
  nlinarith [sq_nonneg x, sq_pos_of_pos hg]

private lemma qcont {g : ℝ} (hg : 0 < g) : Continuous (qlog g) := by
  exact ((continuous_id.pow 2).add continuous_const).log (fun x => (qpos hg x).ne')

private lemma qpcont {g : ℝ} (hg : 0 < g) : Continuous (qprime g) := by
  exact (continuous_const.mul continuous_id).div
    ((continuous_id.pow 2).add continuous_const) (fun x => (qpos hg x).ne')

private lemma qderiv {g : ℝ} (hg : 0 < g) (x : ℝ) :
    HasDerivAt (qlog g) (qprime g x) x := by
  convert (((hasDerivAt_id x).pow 2).add_const (g^2)).log (qpos hg x).ne' using 1 <;>
    (try funext y) <;> (try simp [qlog, qprime, Function.comp_def]) <;> ring

private lemma qpderiv {g : ℝ} (hg : 0 < g) (x : ℝ) :
    HasDerivAt (qprime g) (2 * (g^2 - x^2) / (x^2 + g^2)^2) x := by
  convert ((hasDerivAt_id x).const_mul 2).div
    (((hasDerivAt_id x).pow 2).add_const (g^2)) (qpos hg x).ne' using 1 <;>
    (try funext y) <;> (try simp [qprime, Function.comp_def]) <;> ring

private lemma second_bound {g : ℝ} (hg : 0 < g) (x : ℝ) :
    ‖2 * (g^2 - x^2) / (x^2 + g^2)^2‖ ≤ 2 / g^2 := by
  have hd := qpos hg x
  have hs : |g^2 - x^2| ≤ g^2 + x^2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg g]
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (sq_nonneg (x^2 + g^2))]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hg)).2
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg g)
  nlinarith [mul_nonneg (sq_nonneg x) hd.le]

private lemma kernel_cont {g : ℝ} (hg : 0 < g) (a : ℝ) :
    Continuous (logKernel a g) := by
  exact (((qcont hg).comp (continuous_id.sub continuous_const)).add
    ((qcont hg).comp (continuous_id.add continuous_const))).sub
      (continuous_const.mul (qcont hg))

private lemma kernel_bound {a g : ℝ} (ha : 0 ≤ a) (hg : 0 < g) (t : ℝ) :
    |logKernel a g t| ≤ 2 * a^2 / g^2 := by
  have hlip (x y : ℝ) : ‖qprime g y - qprime g x‖ ≤ (2 / g^2) * ‖y - x‖ := by
    apply Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (fun z _ => (qpderiv hg z).differentiableAt)
      (fun z _ => ?_) convex_univ (Set.mem_univ x) (Set.mem_univ y)
    rw [(qpderiv hg z).deriv]
    exact second_bound hg z
  have hd (v : ℝ) : HasDerivAt (fun v => logKernel v g t)
      (qprime g (t + v) - qprime g (t - v)) v := by
    convert (((qderiv hg (t - v)).comp v
      ((hasDerivAt_const v t).sub (hasDerivAt_id v))).add
      ((qderiv hg (t + v)).comp v
        ((hasDerivAt_const v t).add (hasDerivAt_id v)))).sub_const
          (2 * qlog g t) using 1 <;> (try funext y) <;> (try simp [logKernel, qlog, Function.comp_def]) <;> ring
  have hc : Continuous (fun v => qprime g (t + v) - qprime g (t - v)) :=
    ((qpcont hg).comp (continuous_const.add continuous_id)).sub
      ((qpcont hg).comp (continuous_const.sub continuous_id))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hd v) (hc.intervalIntegrable (μ := volume) 0 a)
  have hzero : logKernel 0 g t = 0 := by
    simp only [logKernel, sub_zero, add_zero]
    ring
  rw [hzero, sub_zero] at hFTC
  have hb : ‖∫ v in (0 : ℝ)..a, qprime g (t + v) - qprime g (t - v)‖ ≤
      ∫ v in (0 : ℝ)..a, (4 / g^2) * v := by
    apply intervalIntegral.norm_integral_le_of_norm_le ha
    · exact Filter.Eventually.of_forall (fun v hv => by
        have h := hlip (t - v) (t + v)
        have he : (t + v) - (t - v) = 2 * v := by ring
        have hv0 : 0 ≤ 2 * v := mul_nonneg (by norm_num) hv.1.le
        simp only [he, Real.norm_eq_abs, abs_of_nonneg hv0] at h
        simpa only [Real.norm_eq_abs] using (show
          |qprime g (t + v) - qprime g (t - v)| ≤ (4 / g^2) * v from by
            convert h using 1 <;> ring))
    · exact (continuous_const.mul continuous_id).intervalIntegrable (μ := volume) 0 a
  rw [hFTC, Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    integral_id] at hb
  convert hb using 1 <;> ring

private lemma edge_cont {g : ℝ} (hg : 0 < g) (T : ℝ) : Continuous (edge g T) := by
  exact ((qcont hg).comp (continuous_const.add continuous_id)).sub
    ((qcont hg).comp (continuous_const.sub continuous_id))

private lemma edge_eq_log {g : ℝ} (hg : 0 < g) (T v : ℝ) :
    edge g T v = Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2)) := by
  exact (Real.log_div (qpos hg (T + v)).ne' (qpos hg (T - v)).ne').symm

private lemma endpoint_eq {g : ℝ} (hg : 0 < g) (a T : ℝ) :
    endpointKernel a g T = ∫ v in (0 : ℝ)..a, edge g T v := by
  apply intervalIntegral.integral_congr
  intro v _
  exact (edge_eq_log hg T v).symm

-- Shifted integral cancellation is valid across negative endpoints as well.
private lemma kernel_integral {g : ℝ} (hg : 0 < g) (a T : ℝ) :
    (∫ t in (0 : ℝ)..T, logKernel a g t) = endpointKernel a g T := by
  let G : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, qlog g u
  have hG (x y : ℝ) : (∫ u in x..y, qlog g u) = G y - G x := by
    exact (intervalIntegral.integral_interval_sub_left
      ((qcont hg).intervalIntegrable (μ := volume) 0 y) ((qcont hg).intervalIntegrable (μ := volume) 0 x)).symm
  have heven (x : ℝ) : qlog g (-x) = qlog g x := by simp [qlog]
  have hodd (x : ℝ) : G (-x) = -G x := by
    have h := intervalIntegral.integral_comp_neg (f := qlog g) (a := 0) (b := x)
    have he : (fun u => qlog g (-u)) = qlog g := funext heven
    rw [he, neg_zero] at h
    have h' : G x = G 0 - G (-x) := by
      calc G x = ∫ u in (-x)..0, qlog g u := h
           _ = G 0 - G (-x) := hG (-x) 0
    have hG0 : G 0 = 0 := by simp [G]
    rw [hG0] at h'
    linarith
  have hm : (∫ t in (0 : ℝ)..T, qlog g (t - a)) = G (T - a) - G (-a) := by
    rw [intervalIntegral.integral_comp_sub_right]
    simpa only [zero_sub] using hG (-a) (T - a)
  have hp : (∫ t in (0 : ℝ)..T, qlog g (t + a)) = G (T + a) - G a := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add] using hG a (T + a)
  have hleft : (∫ t in (0 : ℝ)..T, logKernel a g t) =
      G (T - a) + G (T + a) - 2 * G T := by
    unfold logKernel
    change (∫ t in (0 : ℝ)..T, qlog g (t - a) + qlog g (t + a) - 2 * qlog g t) = _
    have hcm := ((qcont hg).comp (continuous_id.sub (continuous_const (y := a)))).intervalIntegrable (μ := volume) 0 T
    have hcp := ((qcont hg).comp (continuous_id.add (continuous_const (y := a)))).intervalIntegrable (μ := volume) 0 T
    have hc2 := (continuous_const.mul (qcont hg) :
      Continuous (fun t : ℝ => 2 * qlog g t)).intervalIntegrable (μ := volume) 0 T
    rw [intervalIntegral.integral_sub
      (f := fun t => qlog g (t - a) + qlog g (t + a))
      (g := fun t => 2 * qlog g t) (hcm.add hcp) hc2,
      intervalIntegral.integral_add (f := fun t => qlog g (t - a))
        (g := fun t => qlog g (t + a)) hcm hcp, intervalIntegral.integral_const_mul, hm, hp, hodd]
    dsimp [G]
    ring
  rw [hleft, endpoint_eq hg]
  simp only [edge]
  rw [intervalIntegral.integral_sub
    (f := fun v => qlog g (T + v)) (g := fun v => qlog g (T - v))
    (((qcont hg).comp ((continuous_const (y := T)).add continuous_id)).intervalIntegrable (μ := volume) 0 a)
    (((qcont hg).comp ((continuous_const (y := T)).sub continuous_id)).intervalIntegrable (μ := volume) 0 a)]
  have h1 : (∫ v in (0 : ℝ)..a, qlog g (T + v)) = G (T + a) - G T := by
    simp_rw [add_comm T]
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_zero, add_comm] using hG T (T + a)
  have h2 : (∫ v in (0 : ℝ)..a, qlog g (T - v)) = G T - G (T - a) := by
    rw [intervalIntegral.integral_comp_sub_left]
    simpa only [sub_zero] using hG (T - a) T
  rw [h1, h2]
  ring

private lemma edge_nonneg {g T v : ℝ} (hg : 0 < g) (hT : 0 ≤ T) (hv : 0 ≤ v) :
    0 ≤ edge g T v := by
  rw [edge_eq_log hg]
  apply Real.log_nonneg
  apply (one_le_div (qpos hg (T - v))).2
  nlinarith [mul_nonneg hT hv]

private lemma endpoint_nonneg {a g T : ℝ} (ha : 0 ≤ a) (hg : 0 < g) (hT : 0 ≤ T) :
    0 ≤ endpointKernel a g T := by
  rw [endpoint_eq hg]
  exact intervalIntegral.integral_nonneg ha (fun v hv => edge_nonneg hg hT hv.1)

private lemma endpoint_pos {a g T : ℝ} (ha : 0 < a) (hg : 0 < g) (hT : 0 < T) :
    0 < endpointKernel a g T := by
  rw [endpoint_eq hg]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((edge_cont hg T).intervalIntegrable (μ := volume) 0 a) _ ha
  intro v hv
  rw [edge_eq_log hg]
  apply Real.log_pos
  apply (one_lt_div (qpos hg (T - v))).2
  nlinarith [mul_pos hT hv.1]

private lemma edge_bounds {g T v : ℝ} (hg : 0 < g) (hT : 0 ≤ T) (hv : 0 ≤ v) :
    4 * T^2 * v / ((T + v)^2 + g^2) ≤ T * edge g T v ∧
    T * edge g T v ≤ 4 * T^2 * v / ((T - v)^2 + g^2) := by
  have hA := qpos hg (T + v)
  have hB := qpos hg (T - v)
  have hr := div_pos hA hB
  have hl := Real.one_sub_inv_le_log_of_pos hr
  have hu := Real.log_le_sub_one_of_pos hr
  have el : 1 - (((T + v)^2 + g^2) / ((T - v)^2 + g^2))⁻¹ =
      4 * T * v / ((T + v)^2 + g^2) := by
    field_simp [hA.ne', hB.ne'] <;> ring
  have eu : ((T + v)^2 + g^2) / ((T - v)^2 + g^2) - 1 =
      4 * T * v / ((T - v)^2 + g^2) := by
    field_simp [hB.ne'] <;> ring
  rw [el] at hl
  rw [eu] at hu
  rw [edge_eq_log hg]
  constructor
  · convert mul_le_mul_of_nonneg_left hl hT using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hu hT using 1 <;> ring

private lemma endpoint_squeeze {a g T : ℝ} (ha : 0 ≤ a) (hg : 0 < g) (hTa : a ≤ T) :
    2 * a^2 * T^2 / ((T + a)^2 + g^2) ≤ T * endpointKernel a g T ∧
    T * endpointKernel a g T ≤ 2 * a^2 * T^2 / ((T - a)^2 + g^2) := by
  have hT := ha.trans hTa
  have hc := (edge_cont hg T)
  have hE : (∫ v in (0 : ℝ)..a, T * edge g T v) = T * endpointKernel a g T := by
    rw [intervalIntegral.integral_const_mul, endpoint_eq hg]
  have hL := intervalIntegral.integral_mono_on ha
    ((continuous_const.mul continuous_id).intervalIntegrable (μ := volume) 0 a)
    ((continuous_const.mul hc).intervalIntegrable (μ := volume) 0 a)
    (f := fun v => (4 * T^2 / ((T + a)^2 + g^2)) * v)
    (g := fun v => T * edge g T v)
  have hU := intervalIntegral.integral_mono_on ha
    ((continuous_const.mul hc).intervalIntegrable (μ := volume) 0 a)
    ((continuous_const.mul continuous_id).intervalIntegrable (μ := volume) 0 a)
    (f := fun v => T * edge g T v)
    (g := fun v => (4 * T^2 / ((T - a)^2 + g^2)) * v)
  have hl : ∀ v ∈ Set.Icc (0 : ℝ) a,
      (4 * T^2 / ((T + a)^2 + g^2)) * v ≤ T * edge g T v := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have hv1 : v ≤ a := hv.2
    have hb := (edge_bounds hg hT hv.1).1
    have hden : (T + v)^2 + g^2 ≤ (T + a)^2 + g^2 := by
      apply add_le_add _ le_rfl
      exact (sq_le_sq₀ (by linarith : 0 ≤ T + v) (by linarith : 0 ≤ T + a)).2
        (by linarith)
    calc _ = 4 * T^2 * v / ((T + a)^2 + g^2) := by ring
         _ ≤ 4 * T^2 * v / ((T + v)^2 + g^2) :=
           div_le_div_of_nonneg_left (by positivity) (qpos hg (T + v)) hden
         _ ≤ _ := hb
  have hu : ∀ v ∈ Set.Icc (0 : ℝ) a,
      T * edge g T v ≤ (4 * T^2 / ((T - a)^2 + g^2)) * v := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have hv1 : v ≤ a := hv.2
    have hb := (edge_bounds hg hT hv.1).2
    have hden : (T - a)^2 + g^2 ≤ (T - v)^2 + g^2 := by
      apply add_le_add _ le_rfl
      exact (sq_le_sq₀ (by linarith : 0 ≤ T - a) (by linarith : 0 ≤ T - v)).2
        (by linarith)
    calc _ ≤ 4 * T^2 * v / ((T - v)^2 + g^2) := hb
         _ ≤ 4 * T^2 * v / ((T - a)^2 + g^2) :=
           div_le_div_of_nonneg_left (by positivity) (qpos hg (T - a)) hden
         _ = _ := by ring
  have h1 := hL hl
  have h2 := hU hu
  rw [hE, intervalIntegral.integral_const_mul, integral_id] at h1 h2
  constructor
  · convert h1 using 1 <;> ring
  · convert h2 using 1 <;> ring

private lemma endpoint_uniform {a g T : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hg : 0 < g) (hT : 1 ≤ T) :
    0 ≤ T * endpointKernel a g T ∧ T * endpointKernel a g T ≤ 8 * a^2 := by
  have hTa : a ≤ T := by linarith
  refine ⟨mul_nonneg (by linarith) (endpoint_nonneg ha0 hg (by linarith)),
    (endpoint_squeeze ha0 hg hTa).2.trans ?_⟩
  apply (div_le_iff₀ (qpos hg (T - a))).2
  have hhalf : T / 2 ≤ T - a := by linarith
  have hs : (T / 2)^2 ≤ (T - a)^2 :=
    (sq_le_sq₀ (by linarith : 0 ≤ T / 2) (by linarith : 0 ≤ T - a)).2 hhalf
  have hsq : T^2 ≤ 4 * ((T - a)^2 + g^2) := by
    nlinarith [sq_nonneg g]
  have := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hsq)
  nlinarith

private lemma ratio_limit (a g c : ℝ) (hg0 : 0 < g) :
    Tendsto (fun T : ℝ => 2 * a^2 * T^2 / ((T + c)^2 + g^2)) atTop (𝓝 (2 * a^2)) := by
  have hi : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hc : Tendsto (fun T : ℝ => c / T) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := c)).mul hi
  have hg : Tendsto (fun T : ℝ => g / T) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := g)).mul hi
  have hn : Tendsto (fun T : ℝ => 2 * a^2 / ((1 + c / T)^2 + (g / T)^2))
      atTop (𝓝 (2 * a^2)) := by
    convert (tendsto_const_nhds (x := 2 * a^2)).div
      ((((tendsto_const_nhds (x := (1 : ℝ))).add hc).pow 2).add (hg.pow 2))
      (by norm_num : (1 + (0 : ℝ))^2 + 0^2 ≠ 0) using 1 <;> norm_num
  apply hn.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  field_simp [hT.ne', (qpos hg0 (T + c)).ne',
    (qpos (div_pos hg0 hT) (1 + c / T)).ne'] <;> ring

private lemma endpoint_limit {a g : ℝ} (ha : 0 ≤ a) (hg : 0 < g) :
    Tendsto (fun T : ℝ => T * endpointKernel a g T) atTop (𝓝 (2 * a^2)) := by
  apply (ratio_limit a g a hg).squeeze' (by
    simpa only [sub_eq_add_neg] using ratio_limit a g (-a) hg)
  · filter_upwards [eventually_ge_atTop a] with T hT
    exact (endpoint_squeeze ha hg hT).1
  · filter_upwards [eventually_ge_atTop a] with T hT
    exact (endpoint_squeeze ha hg hT).2

-- An arbitrary-filter uniform-to-zero integral theorem avoids any Countable I premise.
private lemma sum_integrals {I : Type*} (f : I → ℝ → ℝ) (F : ℝ → ℝ)
    (hf : ∀ i, Continuous (f i)) (hF : Continuous F)
    (hu : HasSumUniformlyOn f F Set.univ) (T : ℝ) :
    HasSum (fun i => ∫ t in (0 : ℝ)..T, f i t) (∫ t in (0 : ℝ)..T, F t) := by
  classical
  have hunif : TendstoUniformlyOn (fun s : Finset I => fun t => (∑ i ∈ s, f i t) - F t)
      (fun _ => 0) atTop (Set.uIcc 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu.tendstoUniformlyOn ε hε] with s hs t ht
    simpa only [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev] using hs t (Set.mem_univ t)
  have hz := hunif.tendsto_intervalIntegral_nhds_zero (μ := volume)
  have hnet := hz.add (tendsto_const_nhds (x := ∫ t in (0 : ℝ)..T, F t))
  change Tendsto (fun s : Finset I => ∑ i ∈ s, ∫ t in (0 : ℝ)..T, f i t)
    atTop (𝓝 (∫ t in (0 : ℝ)..T, F t))
  convert hnet using 1
  · ext s
    rw [intervalIntegral.integral_sub
      ((continuous_finsetSum s (fun i _ => hf i)).intervalIntegrable (μ := volume) 0 T)
      (hF.intervalIntegrable (μ := volume) 0 T), intervalIntegral.integral_finsetSum
        (fun i _ => (hf i).intervalIntegrable (μ := volume) 0 T)]
    ring
  · simp

private lemma nonnegative_family_limit {I : Type*} (b : I → ℝ) (x : ℝ → I → ℝ)
    (hb0 : ∀ i, 0 ≤ b i)
    (hx0 : ∀ T, 0 ≤ T → ∀ i, 0 ≤ x T i)
    (hxs : ∀ T, 0 ≤ T → Summable (x T))
    (hxl : ∀ i, Tendsto (fun T => x T i) atTop (𝓝 (2 * b i)))
    (hxb : ∀ T, 1 ≤ T → ∀ i, x T i ≤ 8 * b i) :
    Tendsto (fun T => ENNReal.ofReal (∑' i, x T i)) atTop
      (𝓝 (2 * ∑' i, ENNReal.ofReal (b i))) := by
  classical
  by_cases hb : Summable b
  · have hreal : Tendsto (fun T => ∑' i, x T i) atTop (𝓝 (2 * ∑' i, b i)) := by
      have h := tendsto_tsum_of_dominated_convergence (hb.mul_left 8) hxl
        (by
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT i
          rw [Real.norm_eq_abs, abs_of_nonneg (hx0 T (by linarith) i)]
          exact hxb T hT i)
      simpa only [hb.tsum_mul_left 2] using h
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_tsum_of_nonneg hb0 hb] at he
    simpa [Function.comp_def] using he
  · have htop : (∑' i, ENNReal.ofReal (b i)) = ⊤ := by
      by_contra hne
      have hs := ENNReal.summable_toReal hne
      apply hb
      have heq : (fun i => (ENNReal.ofReal (b i)).toReal) = b :=
        funext (fun i => ENNReal.toReal_ofReal (hb0 i))
      rwa [heq] at hs
    have hunbounded (B : ℝ) : ∃ s : Finset I, B < ∑ i ∈ s, b i := by
      by_contra hn
      push_neg at hn
      exact hb (summable_of_sum_le hb0 hn)
    have hdiv : Tendsto (fun T => ∑' i, x T i) atTop atTop := by
      apply tendsto_atTop.2
      intro B
      obtain ⟨s, hs⟩ := hunbounded (max B 0 + 1)
      have hlim := tendsto_finsetSum s (fun i _ => hxl i)
      have hB : B < ∑ i ∈ s, 2 * b i := by
        rw [← Finset.mul_sum]
        have hnonneg : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg (fun i _ => hb0 i)
        have := le_max_left B 0
        linarith
      have hlarge : ∀ᶠ T in atTop, B < ∑ i ∈ s, x T i :=
        (tendsto_order.1 hlim).1 B hB
      filter_upwards [hlarge, eventually_ge_atTop (0 : ℝ)] with T hT hT0
      exact le_trans hT.le ((hxs T hT0).sum_le_tsum s (fun i _ => hx0 T hT0 i))
    simpa [htop] using ENNReal.tendsto_ofReal_nhds_top.mpr hdiv

theorem integrated_transverse_moment {I : Type*} (w a gamma : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1 / 2)
    (hgamma : ∀ i, 0 < gamma i)
    (hbudget : Summable (fun i => w i * (a i)^2 / (gamma i)^2)) :
    (∀ i t, |w i * logKernel (a i) (gamma i) t| ≤
      2 * (w i * (a i)^2 / (gamma i)^2)) ∧
    HasSumUniformlyOn (fun i t => w i * logKernel (a i) (gamma i) t)
      (defect w a gamma) Set.univ ∧
    (∀ t, Summable (fun i => |w i * logKernel (a i) (gamma i) t|)) ∧
    Continuous (defect w a gamma) ∧
    (∀ T : ℝ, 0 ≤ T →
      integratedDefect w a gamma T = ∑' i, w i * endpointKernel (a i) (gamma i) T) ∧
    (∀ T : ℝ, 0 ≤ T → 0 ≤ integratedDefect w a gamma T) ∧
    (∀ T : ℝ, 0 < T →
      (0 < integratedDefect w a gamma T ↔ ∃ i, 0 < w i ∧ 0 < a i)) ∧
    Tendsto (fun T : ℝ => ENNReal.ofReal (T * integratedDefect w a gamma T)) atTop
      (𝓝 (2 * ∑' i, ENNReal.ofReal (w i * (a i)^2))) ∧
    (Tendsto (fun T : ℝ => T * integratedDefect w a gamma T) atTop (𝓝 0) ↔
      ∀ i, 0 < w i → a i = 0) := by
  classical
  let q : I → ℝ := fun i => w i * (a i)^2 / (gamma i)^2
  let f : I → ℝ → ℝ := fun i t => w i * logKernel (a i) (gamma i) t
  have hq : Summable q := hbudget
  have hbound (i : I) (t : ℝ) : |f i t| ≤ 2 * q i := by
    rw [show f i t = w i * logKernel (a i) (gamma i) t from rfl,
      abs_mul, abs_of_nonneg (hw i)]
    have h := mul_le_mul_of_nonneg_left (kernel_bound (ha0 i) (hgamma i) t) (hw i)
    convert h using 1 <;> dsimp [q] <;> ring
  have hnorm (i : I) (t : ℝ) : ‖f i t‖ ≤ 2 * q i := by
    simpa only [Real.norm_eq_abs] using hbound i t
  have hf (i : I) : Continuous (f i) :=
    continuous_const.mul (kernel_cont (hgamma i) (a i))
  have hu : HasSumUniformlyOn f (defect w a gamma) Set.univ :=
    HasSumUniformlyOn.of_norm_le_summable (hq.mul_left 2) (fun i t _ => hnorm i t)
  have habs (t : ℝ) : Summable (fun i => |f i t|) := by
    exact Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => hbound i t)
      (hq.mul_left 2)
  have hc : Continuous (defect w a gamma) := continuous_tsum hf (hq.mul_left 2) hnorm
  have hsum (T : ℝ) : HasSum (fun i => w i * endpointKernel (a i) (gamma i) T)
      (integratedDefect w a gamma T) := by
    change HasSum _ (∫ t in (0 : ℝ)..T, defect w a gamma t)
    convert sum_integrals f (defect w a gamma) hf hc hu T using 1
    ext i
    rw [show f i = (fun t => w i * logKernel (a i) (gamma i) t) from rfl,
      intervalIntegral.integral_const_mul, kernel_integral (hgamma i)]
  have hidentity (T : ℝ) (_ : 0 ≤ T) : integratedDefect w a gamma T =
      ∑' i, w i * endpointKernel (a i) (gamma i) T := (hsum T).tsum_eq.symm
  have hterm (T : ℝ) (hT : 0 ≤ T) (i : I) :
      0 ≤ w i * endpointKernel (a i) (gamma i) T :=
    mul_nonneg (hw i) (endpoint_nonneg (ha0 i) (hgamma i) hT)
  have hnonneg (T : ℝ) (hT : 0 ≤ T) : 0 ≤ integratedDefect w a gamma T := by
    rw [hidentity T hT]
    exact tsum_nonneg (hterm T hT)
  have hstrict (T : ℝ) (hT : 0 < T) :
      (0 < integratedDefect w a gamma T ↔ ∃ i, 0 < w i ∧ 0 < a i) := by
    constructor
    · intro hpos
      by_contra hn
      have hz (i : I) : w i * endpointKernel (a i) (gamma i) T = 0 := by
        by_cases hi : 0 < w i
        · have ha : a i = 0 := le_antisymm
            (le_of_not_gt (fun hia => hn ⟨i, hi, hia⟩)) (ha0 i)
          simp [ha, endpointKernel]
        · have hwz : w i = 0 := le_antisymm (le_of_not_gt hi) (hw i)
          simp [hwz]
      rw [hidentity T hT.le, tsum_congr hz, tsum_zero] at hpos
      exact (lt_irrefl 0) hpos
    · rintro ⟨i, hiw, hia⟩
      rw [hidentity T hT.le]
      exact (hsum T).summable.tsum_pos (hterm T hT.le) i
        (mul_pos hiw (endpoint_pos hia (hgamma i) hT))
  let b : I → ℝ := fun i => w i * (a i)^2
  let x : ℝ → I → ℝ := fun T i => T * (w i * endpointKernel (a i) (gamma i) T)
  have hxsum (T : ℝ) : HasSum (x T) (T * integratedDefect w a gamma T) :=
    (hsum T).mul_left T
  have hx0 (T : ℝ) (hT : 0 ≤ T) (i : I) : 0 ≤ x T i :=
    mul_nonneg hT (hterm T hT i)
  have hxl (i : I) : Tendsto (fun T => x T i) atTop (𝓝 (2 * b i)) := by
    have h := (tendsto_const_nhds (x := w i)).mul
      (endpoint_limit (ha0 i) (hgamma i))
    convert h using 1 <;> (try funext T) <;> simp only [x, b] <;> ring
  have hxb (T : ℝ) (hT : 1 ≤ T) (i : I) : x T i ≤ 8 * b i := by
    have h := mul_le_mul_of_nonneg_left
      (endpoint_uniform (ha0 i) (ha1 i) (hgamma i) hT).2 (hw i)
    convert h using 1 <;> (try funext T) <;> simp only [x, b] <;> ring
  have hlimit : Tendsto (fun T : ℝ => ENNReal.ofReal (T * integratedDefect w a gamma T))
      atTop (𝓝 (2 * ∑' i, ENNReal.ofReal (w i * (a i)^2))) := by
    have h := nonnegative_family_limit b x (fun i => mul_nonneg (hw i) (sq_nonneg _))
      hx0 (fun T _ => (hxsum T).summable) hxl hxb
    have heq : (fun T => ENNReal.ofReal (∑' i, x T i)) =
        (fun T => ENNReal.ofReal (T * integratedDefect w a gamma T)) :=
      funext (fun T => congrArg ENNReal.ofReal (hxsum T).tsum_eq)
    rw [heq] at h
    exact h
  refine ⟨hbound, hu, habs, hc, hidentity, hnonneg, hstrict, hlimit, ?_⟩
  constructor
  · intro hz i hi
    have hzero := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hz
    have heq : (2 : ℝ≥0∞) * (∑' j, ENNReal.ofReal (w j * (a j)^2)) = 0 :=
      tendsto_nhds_unique hlimit (by simpa only [Function.comp_def, ENNReal.ofReal_zero] using hzero)
    have hs0 : (∑' j, ENNReal.ofReal (w j * (a j)^2)) = 0 := by
      exact (mul_eq_zero.mp heq).resolve_left (by norm_num)
    have hi0 : ENNReal.ofReal (w i * (a i)^2) = 0 := by
      exact le_antisymm ((ENNReal.le_tsum i).trans_eq hs0) bot_le
    have hb0 : w i * (a i)^2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hi0
    have ha2 : (a i)^2 = 0 := by
      have : 0 ≤ w i * (a i)^2 := mul_nonneg (hw i) (sq_nonneg _)
      have hzprod : w i * (a i)^2 = 0 := le_antisymm hb0 this
      exact (mul_eq_zero.mp hzprod).resolve_left hi.ne'
    exact sq_eq_zero_iff.mp ha2
  · intro hz
    have hfzero (i : I) (t : ℝ) : w i * logKernel (a i) (gamma i) t = 0 := by
      by_cases hi : 0 < w i
      · rw [hz i hi]
        have hk : logKernel 0 (gamma i) t = 0 := by
          simp only [logKernel, sub_zero, add_zero]
          ring
        rw [hk, mul_zero]
      · have hi0 : w i = 0 := le_antisymm (le_of_not_gt hi) (hw i)
        simp [hi0]
    have hdz : defect w a gamma = 0 := by
      funext t
      change (∑' i, w i * logKernel (a i) (gamma i) t) = 0
      simp only [hfzero, tsum_zero]
    simpa [integratedDefect, hdz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))

end D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment
