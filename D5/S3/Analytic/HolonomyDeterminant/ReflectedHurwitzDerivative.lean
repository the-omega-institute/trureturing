/- GID: D5/S3/Analytic/HolonomyDeterminant/ReflectedHurwitzDerivative
   generality: G
   mirror-B: D5/B/S3/Analytic/HolonomyDeterminant/ReflectedHurwitzDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regularized Hurwitz sums give Lerch's derivative formula on the open unit interval. -/

import D5.S3.Analytic.HolonomyDeterminant.MasslessHolonomyDeterminant
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
For 0 < a < 1, subtract the Riemann partial sum from the Hurwitz partial sum
and add (1-a) N^(-s). Its increments are linear interpolation errors for x^(-s).
Two applications of the mean value inequality bound them by 24 N^(-3/2) on
|s-1| < 3/2. Uniform convergence and analytic continuation identify the limit
with the difference of the two zeta functions. Convergence of holomorphic
derivatives and the Bohr-Mollerup limit for log Gamma then prove Lerch's formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex HurwitzZeta Filter Set
open scoped Topology

namespace D5.S3.Analytic.HolonomyDeterminant.ReflectedHurwitzDerivative

open D5.S3.Analytic.HolonomyDeterminant.MasslessHolonomyDeterminant

private theorem interpolation_bound {f f' f'' : ℝ → ℂ} {n a C : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hC : 0 ≤ C)
    (hf : ∀ x ∈ Icc n (n + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc n (n + 1), HasDerivAt f' (f'' x) x)
    (hb : ∀ x ∈ Icc n (n + 1), ‖f'' x‖ ≤ C) :
    ‖f (n + a) - (a : ℂ) * f (n + 1) - (1 - a : ℂ) * f n‖ ≤ 2 * C := by
  let g := fun x : ℝ => f x - f n - (x - n : ℝ) • f' n
  have hg : ∀ x ∈ Icc n (n + 1), HasDerivAt g (f' x - f' n) x := by
    intro x hx
    simpa only [g, Pi.sub_apply, one_smul, id_eq] using ((hf x hx).sub_const (f n)).fun_sub
      (((hasDerivAt_id x).sub_const n).smul_const (f' n))
  have hbd : ∀ x ∈ Icc n (n + 1), ‖f' x - f' n‖ ≤ C := by
    intro x hx
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun y hy => (hf' y hy).hasDerivWithinAt)
      (fun y hy => hb y (Ico_subset_Icc_self hy)) x hx
    exact h.trans (by nlinarith [hx.2])
  have hbg : ∀ x ∈ Icc n (n + 1), ‖g x‖ ≤ C := by
    intro x hx
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun y hy => (hg y hy).hasDerivWithinAt)
      (fun y hy => hbd y (Ico_subset_Icc_self hy)) x hx
    have hgn : g n = 0 := by simp [g]
    rw [hgn, sub_zero] at h
    exact h.trans (by nlinarith [hx.2])
  have heq : f (n + a) - (a : ℂ) * f (n + 1) - (1 - a : ℂ) * f n =
      g (n + a) - (a : ℂ) * g (n + 1) := by
    simp [g, Complex.real_smul]
    ring
  rw [heq]
  calc
    _ ≤ ‖g (n + a)‖ + ‖(a : ℂ) * g (n + 1)‖ := norm_sub_le _ _
    _ ≤ C + C := by
      gcongr
      · exact hbg _ ⟨by linarith [ha.1], by linarith [ha.2]⟩
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.1]
        exact (mul_le_mul_of_nonneg_left (hbg _ ⟨by linarith, le_rfl⟩) ha.1).trans
          (by nlinarith [ha.2])
    _ = 2 * C := by ring

private theorem cpow_real_derivative (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
      ((-s) * (x : ℂ) ^ (-s - 1)) x := by
  simpa using ((Complex.hasStrictDerivAt_cpow_const
    (c := -s) (ofReal_mem_slitPlane.mpr hx)).hasDerivAt).comp_ofReal

private theorem cpow_real_second_derivative (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (-s) * (y : ℂ) ^ (-s - 1))
      (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
  have h := ((Complex.hasStrictDerivAt_cpow_const
    (c := -s - 1) (ofReal_mem_slitPlane.mpr hx)).hasDerivAt).comp_ofReal.const_mul (-s)
  have hexp : -s - 1 - 1 = -s - 2 := by ring
  have hcoeff : -s * (-s - 1) = s * (s + 1) := by ring
  simpa only [hexp, ← mul_assoc, hcoeff] using h

private theorem cpow_interpolation_bound {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re) :
    ‖((N : ℝ) + a : ℂ) ^ (-s) - (a : ℂ) * (N + 1 : ℂ) ^ (-s) -
      (1 - a : ℂ) * (N : ℂ) ^ (-s)‖ ≤
        2 * (‖s‖ * ‖s + 1‖) * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNge : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hb : ∀ x ∈ Icc (N : ℝ) (N + 1),
      ‖s * (s + 1) * (x : ℂ) ^ (-s - 2)‖ ≤
        ‖s‖ * ‖s + 1‖ * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro x hx
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos (hNpos.trans_le hx.1)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simp only [sub_re, neg_re, show (2 : ℂ).re = (2 : ℝ) by norm_num]
    exact (Real.rpow_le_rpow_of_nonpos hNpos hx.1 (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hNge (by linarith))
  have h := interpolation_bound ha (by positivity)
    (fun x hx => cpow_real_derivative s (hNpos.trans_le hx.1))
    (fun x hx => cpow_real_second_derivative s (hNpos.trans_le hx.1)) hb
  simpa only [ofReal_add, ofReal_natCast, ofReal_one, mul_assoc] using h

private noncomputable def increment (a : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ((N : ℝ) + a : ℂ) ^ (-s) - (a : ℂ) * (N + 1 : ℂ) ^ (-s) -
    (1 - a : ℂ) * (N : ℂ) ^ (-s)

private theorem increment_bound {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) {N : ℕ} (hN : 0 < N)
    {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (3 / 2)) :
    ‖increment a N s‖ ≤ 24 * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hd : ‖s - 1‖ < 3 / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hsr : -(1 / 2 : ℝ) < s.re := by
    have h := (abs_le.mp (abs_re_le_norm (s - 1))).1
    simp only [sub_re, one_re] at h
    linarith
  have hn : ‖s‖ < 3 := by
    have h := norm_add_le (s - 1) 1
    simp only [sub_add_cancel, norm_one] at h
    linarith
  have hn' : ‖s + 1‖ < 4 := by
    have h := norm_add_le s 1
    simp only [norm_one] at h
    linarith
  exact (cpow_interpolation_bound ha hN hsr).trans
    (mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg s, norm_nonneg (s + 1)])
      (Real.rpow_nonneg (Nat.cast_nonneg N) _))

private noncomputable def regularizedSum (a : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range N, (((n : ℝ) + a : ℝ) : ℂ) ^ (-s)) -
    (∑ n ∈ Finset.range N, (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) +
    (1 - a : ℂ) * (N : ℂ) ^ (-s)

private theorem regularizedSum_step (a : ℝ) (N : ℕ) (s : ℂ) :
    regularizedSum a (N + 1) s - regularizedSum a N s = increment a N s := by
  simp only [regularizedSum, increment, Finset.sum_range_succ]
  push_cast
  ring

private theorem regularizedSum_telescope (a : ℝ) (N : ℕ) (s : ℂ) :
    regularizedSum a (N + 1) s = regularizedSum a 1 s +
      ∑ n ∈ Finset.range N, increment a (n + 1) s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := regularizedSum_step a (N + 1) s
    rw [ih] at h
    linear_combination h

private noncomputable def regularizedLimit (a : ℝ) (s : ℂ) : ℂ :=
  regularizedSum a 1 s + ∑' n : ℕ, increment a (n + 1) s

private theorem regularizedSum_uniform (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    TendstoUniformlyOn (fun N => regularizedSum a (N + 1)) (regularizedLimit a) atTop
      (Metric.ball (1 : ℂ) (3 / 2)) := by
  have hu : Summable (fun n : ℕ => 24 * (n + 1 : ℝ) ^ (-(3 / 2 : ℝ))) := by
    have h := (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 24
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  have ht := tendstoUniformlyOn_tsum_nat (f := fun n => increment a (n + 1)) hu
    (fun n s hs => by simpa only [Nat.cast_succ] using increment_bound ha (Nat.succ_pos n) hs)
  rw [Metric.tendstoUniformlyOn_iff] at ht ⊢
  intro ε hε
  filter_upwards [ht ε hε] with N hN s hs
  rw [regularizedLimit, regularizedSum_telescope a N, dist_add_left]
  exact hN s hs

private theorem regularizedSum_differentiable (a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 0 < N) :
    Differentiable ℂ (regularizedSum a N) := by
  intro s
  have hn : DifferentiableAt ℂ (fun s : ℂ => -s) s := differentiableAt_id.neg
  apply DifferentiableAt.add
  · apply DifferentiableAt.sub
    · exact DifferentiableAt.fun_sum fun n _ => hn.const_cpow
        (Or.inl (by exact_mod_cast (show (n : ℝ) + a ≠ 0 by positivity)))
    · exact DifferentiableAt.fun_sum fun n _ => hn.const_cpow
        (Or.inl (by exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)))
  · exact (hn.const_cpow
      (Or.inl (by exact_mod_cast hN.ne'))).const_mul (1 - a : ℂ)

private theorem regularizedLimit_differentiableOn (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    DifferentiableOn ℂ (regularizedLimit a) (Metric.ball (1 : ℂ) (3 / 2)) := by
  apply (regularizedSum_uniform a ⟨ha.1.le, ha.2.le⟩).tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall (fun N => (regularizedSum_differentiable a ha.1 (N + 1)
      (Nat.succ_pos N)).differentiableOn)) Metric.isOpen_ball

private theorem nat_cpow_neg_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (-s)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply ((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [norm_natCast_cpow_of_pos hN, neg_re]
  rfl

private theorem regularizedSum_tendsto_dirichlet (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => regularizedSum a N s) atTop
      (𝓝 (hurwitzZeta (a : UnitAddCircle) s - hurwitzZeta 0 s)) := by
  have h₁ : Tendsto (fun N => ∑ n ∈ Finset.range N, (n + (a : ℂ)) ^ (-s)) atTop
      (𝓝 (hurwitzZeta (a : UnitAddCircle) s)) := by
    simpa only [cpow_neg, one_div] using
      (hasSum_hurwitzZeta_of_one_lt_re ha hs).tendsto_sum_nat
  have h₂ : Tendsto (fun N => ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)) atTop
      (𝓝 (hurwitzZeta 0 s)) := by
    simpa only [cpow_neg, one_div, ofReal_one, AddCircle.coe_period] using
      (hasSum_hurwitzZeta_of_one_lt_re (show (1 : ℝ) ∈ Icc 0 1 by simp) hs).tendsto_sum_nat
  have h₃ := (nat_cpow_neg_tendsto (by linarith : 0 < s.re)).const_mul (1 - a : ℂ)
  simpa only [regularizedSum, cpow_neg, one_div, ofReal_add, ofReal_natCast,
    ofReal_one, AddCircle.coe_period, mul_zero, add_zero] using (h₁.sub h₂).add h₃

private theorem regularizedLimit_eq (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    EqOn (regularizedLimit a)
      (fun s => hurwitzZeta (a : UnitAddCircle) s - hurwitzZeta 0 s)
      (Metric.ball (1 : ℂ) (3 / 2)) := by
  let U := Metric.ball (1 : ℂ) (3 / 2)
  have hU : IsOpen U := Metric.isOpen_ball
  have htwo : (2 : ℂ) ∈ U := by norm_num [U, Metric.mem_ball, dist_eq_norm]
  have hf := (regularizedLimit_differentiableOn a ha).analyticOnNhd hU
  have hg := (differentiable_hurwitzZeta_sub_hurwitzZeta (a : UnitAddCircle) 0).differentiableOn.analyticOnNhd hU
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_ball (1 : ℂ) (3 / 2)).isPreconnected htwo
  have hV : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  filter_upwards [hV, hU.mem_nhds htwo] with s hs hsU
  apply tendsto_nhds_unique ((regularizedSum_uniform a ⟨ha.1.le, ha.2.le⟩).tendsto_at hsU)
  exact (regularizedSum_tendsto_dirichlet a ⟨ha.1.le, ha.2.le⟩ hs).comp (tendsto_add_atTop_nat 1)

private theorem regularizedSum_derivative_tendsto (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun N => deriv (regularizedSum a (N + 1)) 0) atTop
      (𝓝 (deriv (fun s => hurwitzZeta (a : UnitAddCircle) s - hurwitzZeta 0 s) 0)) := by
  have ht := (regularizedSum_uniform a ⟨ha.1.le, ha.2.le⟩).congr_right (regularizedLimit_eq a ha)
  exact (ht.tendstoLocallyUniformlyOn.deriv
    (Eventually.of_forall fun N => (regularizedSum_differentiable a ha.1 (N + 1)
      (Nat.succ_pos N)).differentiableOn) Metric.isOpen_ball).tendsto_at
    (by norm_num [Metric.mem_ball, dist_eq_norm])

private theorem hasDerivAt_neg_cpow (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s : ℂ => (x : ℂ) ^ (-s)) (-(Real.log x : ℂ)) 0 := by
  have h := (hasDerivAt_id (0 : ℂ)).neg.const_cpow
    (c := (x : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  simpa only [Pi.neg_apply, id_eq, neg_zero, cpow_zero, one_mul, mul_neg,
    mul_one, Complex.ofReal_log hx.le] using h

private theorem regularizedSum_derivative (a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 0 < N) :
    deriv (regularizedSum a N) 0 =
      ((Real.BohrMollerup.logGammaSeq a N + Real.log (N + a) - Real.log N : ℝ) : ℂ) := by
  have h₁ := HasDerivAt.fun_sum (u := Finset.range N)
    (fun n _ => hasDerivAt_neg_cpow (n + a) (by positivity))
  have h₂ := HasDerivAt.fun_sum (u := Finset.range N)
    (fun n _ => hasDerivAt_neg_cpow (n + 1) (by positivity))
  have h₃ := (hasDerivAt_neg_cpow N (by exact_mod_cast hN)).const_mul (1 - a : ℂ)
  have h := ((h₁.sub h₂).add h₃).deriv
  change deriv (regularizedSum a N) 0 = _ at h
  rw [h]
  have hfact : Real.log (N.factorial : ℝ) =
      ∑ n ∈ Finset.range N, Real.log ((n : ℝ) + 1) := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod,
      Real.log_prod (fun n _ => by positivity)]
    simp only [Nat.cast_add, Nat.cast_one]
  simp only [Real.BohrMollerup.logGammaSeq, Finset.sum_range_succ, hfact]
  push_cast
  simp only [Finset.sum_neg_distrib]
  simp_rw [add_comm a]
  ring

private theorem regularizedSum_derivative_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => deriv (regularizedSum a N) 0) atTop
      (𝓝 ((Real.log (Real.Gamma a) : ℝ) : ℂ)) := by
  have ht := (Real.BohrMollerup.tendsto_log_gamma ha).add
    ((Real.tendsto_log_comp_add_sub_log a).comp tendsto_natCast_atTop_atTop)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  simp only [add_zero] at hc
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [regularizedSum_derivative a ha N hN]
  simp only [Function.comp_apply, add_sub_assoc]

private theorem hurwitz_derivative_at_zero (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    deriv (hurwitzZeta (a : UnitAddCircle)) 0 =
      ((Real.log (Real.Gamma a) - Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) := by
  have h := tendsto_nhds_unique (regularizedSum_derivative_tendsto a ha)
    ((regularizedSum_derivative_limit a ha.1).comp (tendsto_add_atTop_nat 1))
  rw [deriv_fun_sub (differentiableAt_hurwitzZeta _ (by norm_num))
    (differentiableAt_hurwitzZeta _ (by norm_num)), hurwitzZeta_zero,
    deriv_riemannZeta_zero] at h
  have hlog : Complex.log (2 * (Real.pi : ℂ)) = (Real.log (2 * Real.pi) : ℂ) := by
    simpa only [ofReal_mul, ofReal_ofNat] using
      (Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).symm
  rw [hlog] at h
  push_cast
  linear_combination h

/-- Lerch's formula at zero for both reflected holonomies in the open unit interval. -/
theorem has_reflected_hurwitz_derivative_at_zero_formula
    (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) : HasReflectedHurwitzDerivativeAtZeroFormula a := by
  refine ⟨hurwitz_derivative_at_zero a ha, ?_⟩
  have href : ((1 - a : ℝ) : UnitAddCircle) = reflectedHolonomy a := by
    rw [reflectedHolonomy, AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  rw [← href]
  exact hurwitz_derivative_at_zero (1 - a) ⟨by linarith [ha.2], by linarith [ha.1]⟩

#print axioms has_reflected_hurwitz_derivative_at_zero_formula

end D5.S3.Analytic.HolonomyDeterminant.ReflectedHurwitzDerivative
