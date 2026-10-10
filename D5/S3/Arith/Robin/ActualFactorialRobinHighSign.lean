/- GID: D5/S3/Arith/Robin/ActualFactorialRobinHighSign
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualFactorialRobinHighSign
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Positive Laplace transport of the literal factorial high weight and natural odd prefixes. -/
import D5.S3.Arith.Robin.ActualFactorialRobinHighWeight
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
The intended consumer is the strict negative sign of the EXACT natural range-N
odd high q-prefix, excluding the unit. No absolute summability of that final
real family is used. Gamma, Tonelli, finite Abel and Dirichlet inversion are
classical consumed suppliers, not new mathematical products or priority claims.
The original signed factorial cumulative mass and q remain at their owners.
See the owning Scribe for the remaining full Robin terms.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace D5.S3.Arith.Robin.ActualFactorialRobinHighSign
open ActualFactorialCumulativePositivity (cumulative tailKernel)
open ActualFactorialRobinHighDerivative (highRemainder)
open ActualFactorialRobinHighWeight (q naturalPrefix)
open ActualOddHarmonicMobiusTail (oddHarmonicPrefix weightedOddTail)

/-- The Laplace transform of the literal positive cumulative signed mass. -/
def Ahat (t : ℝ) : ℝ :=
  ∫ y in Ioi (1 : ℝ), cumulative y / y * Real.exp (-t * Real.log y)

/-- Density for the actual dyadic difference q, with its factor one half. -/
def nu (t : ℝ) : ℝ :=
  t * (1 + t) * (1 - Real.exp (-t * Real.log 2) / 2) * Ahat t

private def joint (r : ℝ) (p : ℝ × ℝ) : ℝ :=
  cumulative p.1 / p.1 * (p.2 * (1 + p.2) *
    Real.exp (-((r + Real.log p.1) * p.2)))

private lemma cumulative_measurable :
    AEStronglyMeasurable cumulative (volume.restrict (Ioi (1 : ℝ))) := by
  have hi := (ActualFactorialCumulativePositivity.result.2.2.2.2.2.2 1 (by norm_num)).1
  have hm : Measurable (fun y : ℝ => (tailKernel 1 y)⁻¹) := by
    unfold tailKernel
    fun_prop
  apply (hi.aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hd : 0 < 1 + Real.log y := by linarith [Real.log_pos hy]
  have hk : tailKernel 1 y ≠ 0 := by unfold tailKernel; positivity
  exact mul_inv_cancel_right₀ hk (cumulative y)

private lemma gamma_integrable {r : ℝ} (hr : 0 < r) (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(r*t))) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (k : ℝ)) (p := 1) (b := r)
    (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by norm_num) hr
  simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using h

private lemma gamma_kernel_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t * (1+t) * Real.exp (-(r*t))) (Ioi (0 : ℝ)) := by
  apply ((gamma_integrable hr 1).add (gamma_integrable hr 2)).congr
  filter_upwards with t
  dsimp only [Pi.add_apply]
  ring

private lemma gamma_kernel {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), t * (1+t) * Real.exp (-(r*t))) =
      r⁻¹ ^ 2 + 2 * r⁻¹ ^ 3 := by
  have h2 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  have h3 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (by norm_num) hr
  have hg2 : Real.Gamma 2 = 1 := by
    convert Real.Gamma_nat_eq_factorial 1 using 1 <;> norm_num
  have hg3 : Real.Gamma 3 = 2 := by
    convert Real.Gamma_nat_eq_factorial 2 using 1 <;> norm_num
  norm_num [hg2, hg3, Real.rpow_natCast, one_div] at h2 h3
  calc
    _ = (∫ t in Ioi (0 : ℝ), t ^ 1 * Real.exp (-(r*t))) +
        ∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-(r*t)) := by
      rw [← integral_add (gamma_integrable hr 1) (gamma_integrable hr 2)]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = _ := by simp only [pow_one]; rw [h2, h3]; ring

private lemma joint_measurable (r : ℝ) :
    AEStronglyMeasurable (joint r)
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      p.1⁻¹ * (p.2 * (1+p.2) * Real.exp (-((r+Real.log p.1)*p.2)))) := by fun_prop
  apply (cumulative_measurable.comp_fst.mul hm.aestronglyMeasurable).congr
  filter_upwards with p
  dsimp only [Pi.mul_apply, joint]
  ring

private lemma joint_nonneg {r y t : ℝ} (hy : 1 < y) (ht : 0 < t) :
    0 ≤ joint r (y,t) := by
  have hC := (ActualFactorialCumulativePositivity.result.2.2.2.1 y hy).le
  have hy0 : 0 < y := zero_lt_one.trans hy
  dsimp [joint]
  positivity

/- Nonnegative Tonelli is paid here BEFORE any Mobius coefficient appears. -/
private lemma joint_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (joint r)
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  apply (integrable_prod_iff (joint_measurable r)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change IntegrableOn (fun t => cumulative y / y *
      (t*(1+t)*Real.exp (-((r+Real.log y)*t)))) (Ioi (0 : ℝ))
    exact (gamma_kernel_integrable (by linarith [Real.log_pos hy] :
      0 < r+Real.log y)).const_mul (cumulative y / y)
  · apply ((ActualFactorialCumulativePositivity.result.2.2.2.2.2.2 r hr).1).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hd : 0 < r+Real.log y := by linarith [Real.log_pos hy]
    calc
      cumulative y * tailKernel r y =
          cumulative y / y * ((r+Real.log y)⁻¹^2+2*(r+Real.log y)⁻¹^3) := by
        unfold tailKernel
        ring
      _ = ∫ t in Ioi (0 : ℝ), joint r (y,t) := by
        change _ = ∫ t in Ioi (0 : ℝ), cumulative y / y *
          (t*(1+t)*Real.exp (-((r+Real.log y)*t)))
        rw [integral_const_mul, gamma_kernel hd]
      _ = ∫ t in Ioi (0 : ℝ), ‖joint r (y,t)‖ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [Real.norm_eq_abs, abs_of_nonneg (joint_nonneg hy ht)]

private lemma joint_right (r t : ℝ) :
    (∫ y in Ioi (1 : ℝ), joint r (y,t)) =
      t*(1+t)*Ahat t*Real.exp (-(r*t)) := by
  calc
    _ = ∫ y in Ioi (1 : ℝ), (cumulative y / y * Real.exp (-t*Real.log y)) *
        (t*(1+t)*Real.exp (-(r*t))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      dsimp [joint]
      rw [show -((r+Real.log y)*t) = -t*Real.log y+-(r*t) by ring, Real.exp_add]
      ring
    _ = _ := by rw [integral_mul_const]; dsimp [Ahat]; ring

private lemma high_laplace {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t => t*(1+t)*Ahat t*Real.exp (-(r*t))) (Ioi (0 : ℝ)) ∧
    highRemainder r = ∫ t in Ioi (0 : ℝ), t*(1+t)*Ahat t*Real.exp (-(r*t)) := by
  have hi := joint_integrable hr
  refine ⟨hi.integral_prod_right.congr (Eventually.of_forall (joint_right r)), ?_⟩
  rw [ActualFactorialCumulativePositivity.positive_representation_y hr]
  calc
    _ = ∫ y in Ioi (1 : ℝ), ∫ t in Ioi (0 : ℝ), joint r (y,t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      change _ = ∫ t in Ioi (0 : ℝ), cumulative y / y *
        (t*(1+t)*Real.exp (-((r+Real.log y)*t)))
      rw [integral_const_mul, gamma_kernel (by linarith [Real.log_pos hy])]
      unfold tailKernel
      ring
    _ = ∫ t in Ioi (0 : ℝ), ∫ y in Ioi (1 : ℝ), joint r (y,t) := integral_integral_swap hi
    _ = _ := by simp_rw [joint_right]

private lemma q_laplace {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t => nu t * Real.exp (-(r*t))) (Ioi (0 : ℝ)) ∧
    q r = ∫ t in Ioi (0 : ℝ), nu t * Real.exp (-(r*t)) := by
  have hc : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h0 := high_laplace hr
  have h1 := high_laplace (show 0 < r+Real.log 2 by linarith)
  have heq (t : ℝ) :
      t*(1+t)*Ahat t*Real.exp (-(r*t)) -
        t*(1+t)*Ahat t*Real.exp (-((r+Real.log 2)*t))/2 = nu t*Real.exp (-(r*t)) := by
    dsimp [nu]
    rw [show -((r+Real.log 2)*t) = -t*Real.log 2+-(r*t) by ring, Real.exp_add]
    ring
  refine ⟨(h0.1.sub (h1.1.div_const 2)).congr (Eventually.of_forall heq), ?_⟩
  rw [q, h0.2, h1.2, ← integral_div, ← integral_sub h0.1 (h1.1.div_const 2)]
  exact integral_congr_ae (Eventually.of_forall heq)

private lemma exp_div_eq_rpow {y : ℝ} (hy : 0 < y) (t : ℝ) :
    Real.exp (-t*Real.log y) / y = y ^ (-(1+t)) := by
  rw [Real.rpow_def_of_pos hy, show Real.log y * -(1+t) =
    -t*Real.log y + -Real.log y by ring, Real.exp_add, Real.exp_neg, Real.exp_log hy]
  ring

private lemma Ahat_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun y => cumulative y / y * Real.exp (-t*Real.log y)) (Ioi (1 : ℝ)) := by
  have hb := (integrableOn_Ioi_rpow_of_lt (by linarith : -(1+t) < -1)
    (by norm_num : (0 : ℝ) < 1)).const_mul (2 : ℝ)
  have hm : Measurable (fun y : ℝ => y⁻¹ * Real.exp (-t*Real.log y)) := by fun_prop
  refine hb.mono' ?_ ?_
  · apply (cumulative_measurable.mul hm.aestronglyMeasurable).congr
    filter_upwards with y
    dsimp only [Pi.mul_apply]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hC := ActualFactorialCumulativePositivity.result.2.2.2.1 y hy
    have hC2 := (ActualFactorialCumulativePositivity.result.2.2.1 y hy.le).2.2
    have hy0 : 0 < y := zero_lt_one.trans hy
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      _ = cumulative y * y ^ (-(1+t)) := by
        rw [← exp_div_eq_rpow (zero_lt_one.trans hy)]
        ring
      _ ≤ 2 * y ^ (-(1+t)) := mul_le_mul_of_nonneg_right hC2.le (by positivity)

private lemma Ahat_bounds {t : ℝ} (ht : 0 < t) : 0 < Ahat t ∧ Ahat t ≤ 2/t := by
  have hi := Ahat_integrable ht
  have hp (y : ℝ) (hy : y ∈ Ioi (1 : ℝ)) :
      0 < cumulative y / y * Real.exp (-t*Real.log y) := by
    have hC := ActualFactorialCumulativePositivity.result.2.2.2.1 y hy
    have hy0 : 0 < y := zero_lt_one.trans hy
    positivity
  constructor
  · apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => (hp y hy).le)) hi).mpr
    have hsub : Ioo (1 : ℝ) 2 ⊆
        Function.support (fun y => cumulative y / y * Real.exp (-t*Real.log y)) ∩ Ioi 1 :=
      fun y hy => ⟨(hp y hy.1).ne', hy.1⟩
    exact (show 0 < volume (Ioo (1 : ℝ) 2) by norm_num [Real.volume_Ioo]).trans_le
      (measure_mono hsub)
  · calc
      Ahat t ≤ ∫ y in Ioi (1 : ℝ), 2 * y ^ (-(1+t)) := by
        apply setIntegral_mono_on hi
          ((integrableOn_Ioi_rpow_of_lt (by linarith : -(1+t) < -1)
            (by norm_num : (0 : ℝ) < 1)).const_mul 2) measurableSet_Ioi
        intro y hy
        have hy0 : 0 < y := zero_lt_one.trans hy
        have hC := (ActualFactorialCumulativePositivity.result.2.2.1 y hy.le).2.2
        rw [show cumulative y / y * Real.exp (-t*Real.log y) =
          cumulative y * (Real.exp (-t*Real.log y)/y) by ring,
          exp_div_eq_rpow (zero_lt_one.trans hy)]
        exact mul_le_mul_of_nonneg_right hC.le (by positivity)
      _ = 2/t := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -(1+t) < -1)
          (by norm_num : (0 : ℝ) < 1), Real.one_rpow]
        rw [show -(1+t)+1 = -t by ring]
        field_simp [ht.ne'] <;> ring

private lemma Ahat_measurable :
    AEStronglyMeasurable Ahat (volume.restrict (Ioi (0 : ℝ))) := by
  have hi := (high_laplace (by norm_num : (0 : ℝ) < 1)).1
  have hm : Measurable (fun t : ℝ => (t*(1+t)*Real.exp (-(1*t)))⁻¹) := by fun_prop
  apply (hi.aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hn : t*(1+t)*Real.exp (-(1*t)) ≠ 0 := by positivity
  change (t*(1+t)*Ahat t*Real.exp (-(1*t))) *
    (t*(1+t)*Real.exp (-(1*t)))⁻¹ = Ahat t
  calc
    _ = Ahat t * (t*(1+t)*Real.exp (-(1*t))) *
        (t*(1+t)*Real.exp (-(1*t)))⁻¹ := by ring
    _ = _ := mul_inv_cancel_right₀ hn _

private lemma nu_measurable :
    AEStronglyMeasurable nu (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : Measurable (fun t : ℝ => t*(1+t)*(1-Real.exp (-t*Real.log 2)/2)) := by fun_prop
  exact hm.aestronglyMeasurable.mul Ahat_measurable

private lemma nu_bounds {t : ℝ} (ht : 0 < t) : 0 < nu t ∧ nu t ≤ 2*(1+t) := by
  obtain ⟨ha0, ha2⟩ := Ahat_bounds ht
  have he : Real.exp (-t*Real.log 2) ≤ 1 := Real.exp_le_one_iff.mpr
    (by have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2); nlinarith)
  have hfac : 0 < 1-Real.exp (-t*Real.log 2)/2 := by linarith
  have hfac1 : 1-Real.exp (-t*Real.log 2)/2 ≤ 1 := by linarith [Real.exp_pos (-t*Real.log 2)]
  constructor
  · dsimp [nu]; positivity
  · calc
      nu t ≤ t*(1+t)*1*(2/t) := by
        dsimp [nu]
        gcongr
      _ = 2*(1+t) := by field_simp [ht.ne'] <;> ring

/-- The natural exclusive arithmetic prefix used under the positive Laplace integral. -/
def S (N : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ (Finset.range N).filter (fun m => Odd m ∧ 3 ≤ m),
    (ArithmeticFunction.moebius m : ℝ)/(m : ℝ)*Real.exp (-t*Real.log m)

private lemma S_bound (N : ℕ) {t : ℝ} (ht : 0 < t) :
    |S N t| ≤ 3*Real.exp (-t*Real.log 3) := by
  classical
  by_cases hN : N ≤ 3
  · have hz : (Finset.range N).filter (fun m => Odd m ∧ 3 ≤ m) = ∅ := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      omega
    simp only [S, hz, Finset.sum_empty, abs_zero]
    positivity
  have h2 : oddHarmonicPrefix 2 = 1 := by
    have he : oddHarmonicPrefix 2 = oddHarmonicPrefix 1 := by
      norm_num [oddHarmonicPrefix, Finset.sum_filter,
        show Finset.Ioc 0 2 = {1,2} by decide,
        show Finset.Ioc 0 1 = {1} by decide]
    exact he.trans ActualOddHarmonicMobiusTail.result.2.1
  have hb := ActualOddHarmonicMobiusTail.result.2.2.2 2 (N-1)
    (by omega) (fun m => Real.exp (-t*Real.log m))
    (fun _ _ => (Real.exp_pos _).le) (by
      intro m hm n hn hmn
      have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by have := hm.1; omega)
      apply Real.exp_le_exp.mpr
      have hl : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log hm0 (by exact_mod_cast hmn)
      nlinarith)
  rw [h2] at hb
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, sub_self, sub_zero,
    show (-2 - 1 : ℝ) = -3 by norm_num,
    show (2 - 1 : ℝ) = 1 by norm_num, one_mul] at hb
  have hid : S N t = weightedOddTail 2 (N-1) (fun m => Real.exp (-t*Real.log m)) := by
    unfold S weightedOddTail
    apply Finset.sum_congr ?_ (by intros; rfl)
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hmN, ho, hm3⟩
      exact ⟨⟨by omega, by omega⟩, ho⟩
    · rintro ⟨⟨hm2, hmN⟩, ho⟩
      exact ⟨by omega, ho, by omega⟩
  rw [hid]
  apply abs_le.mpr
  constructor <;> nlinarith [hb.1, hb.2.1, Real.exp_pos (-t*Real.log 3)]

private lemma prefix_integral (N : ℕ) :
    naturalPrefix N = ∫ t in Ioi (0 : ℝ), nu t*S N t := by
  classical
  simp only [naturalPrefix, S, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    have hm3 := (Finset.mem_filter.mp hm).2.2
    have hl : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    rw [(q_laplace hl).2, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [show -(Real.log (m : ℝ)*t) = -t*Real.log m by ring]
    ring
  · intro m hm
    have hm3 := (Finset.mem_filter.mp hm).2.2
    have hl : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    apply ((q_laplace hl).1.const_mul ((ArithmeticFunction.moebius m : ℝ)/(m : ℝ))).congr
    filter_upwards with t
    rw [show -(Real.log (m : ℝ)*t) = -t*Real.log m by ring]
    ring

private def chi : DirichletCharacter ℂ 2 := 1

private def zcoeff (t : ℝ) (n : ℕ) : ℝ :=
  if Odd n then ((n : ℝ) ^ (1+t))⁻¹ else 0

private def ecoeff (t : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ)*zcoeff t n

private def Z (t : ℝ) : ℝ := ∑' n : ℕ, zcoeff t n
private def E (t : ℝ) : ℝ := ∑' n : ℕ, ecoeff t n

private lemma chi_eq (n : ℕ) : chi n = if Odd n then (1 : ℂ) else 0 := by
  classical
  change (1 : MulChar (ZMod 2) ℂ) (n : ZMod 2) = _
  by_cases hn : Odd n
  · rw [if_pos hn]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n 2).mpr hn.coprime_two_right)
  · rw [if_neg hn]
    apply MulChar.map_nonunit
    simpa only [ZMod.isUnit_iff_coprime, Nat.coprime_two_right] using hn

private lemma zterm (t : ℝ) (n : ℕ) :
    LSeries.term (fun n : ℕ => chi n) ((1+t : ℝ) : ℂ) n = (zcoeff t n : ℂ) := by
  classical
  by_cases hn : n = 0
  · simp [hn, zcoeff]
  rw [LSeries.term_of_ne_zero hn, chi_eq]
  dsimp [zcoeff]
  split_ifs with ho
  · rw [one_div, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_cast
  · simp

private lemma eterm (t : ℝ) (n : ℕ) :
    LSeries.term (fun n : ℕ => chi n*(ArithmeticFunction.moebius n : ℂ))
      ((1+t : ℝ) : ℂ) n = (ecoeff t n : ℂ) := by
  classical
  by_cases hn : n = 0
  · simp [hn, ecoeff, zcoeff]
  have hz := zterm t n
  rw [LSeries.term_of_ne_zero hn] at hz ⊢
  dsimp [ecoeff]
  push_cast
  push_cast at hz
  rw [mul_comm (chi n), mul_div_assoc, hz]

private lemma z_summable {t : ℝ} (ht : 0 < t) : Summable (zcoeff t) := by
  have h := DirichletCharacter.LSeriesSummable_of_one_lt_re chi
    (s := ((1+t : ℝ) : ℂ)) (by simpa using (show 1 < 1+t by linarith))
  apply Complex.summable_ofReal.mp
  exact h.congr (zterm t)

private lemma e_summable {t : ℝ} (ht : 0 < t) : Summable (ecoeff t) := by
  have hs : 1 < ((1+t : ℝ) : ℂ).re := by simpa using (show 1 < 1+t by linarith)
  have h := DirichletCharacter.LSeriesSummable_mul chi
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  apply Complex.summable_ofReal.mp
  exact h.congr (eterm t)

private lemma ze_inverse {t : ℝ} (ht : 0 < t) : Z t * E t = 1 := by
  have hs : 1 < ((1+t : ℝ) : ℂ).re := by simpa using (show 1 < 1+t by linarith)
  have h := DirichletCharacter.LSeries.mul_mu_eq_one chi hs
  change LSeries (fun n : ℕ => chi n) ((1+t : ℝ) : ℂ) *
    LSeries (fun n : ℕ => chi n*(ArithmeticFunction.moebius n : ℂ))
      ((1+t : ℝ) : ℂ) = 1 at h
  simp only [LSeries, zterm, eterm, ← Complex.ofReal_tsum] at h
  exact_mod_cast h

private lemma z_nonneg (t : ℝ) (n : ℕ) : 0 ≤ zcoeff t n := by
  unfold zcoeff
  split_ifs <;> positivity

private lemma Z_one_le {t : ℝ} (ht : 0 < t) : 1 ≤ Z t := by
  have h := (z_summable ht).sum_le_tsum {1} (fun n _ => z_nonneg t n)
  simpa [Z, zcoeff] using h

private lemma z_prime_powers (t : ℝ) (j : ℕ) :
    zcoeff t (3^j) = (Real.exp (-(1+t)*Real.log 3))^j := by
  have ho : Odd ((3 : ℕ)^j) := (by decide : Odd (3 : ℕ)).pow
  simp only [zcoeff, if_pos ho, Nat.cast_pow]
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, ← Real.exp_neg,
    ← Real.exp_nat_mul]
  congr 1
  ring

private lemma E_margin {t : ℝ} (ht : 0 < t) :
    E t-1 ≤ -Real.exp (-t*Real.log 3)/3 := by
  let a := Real.exp (-(1+t)*Real.log 3)
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr
    (by have hl := Real.log_pos (by norm_num : (1 : ℝ) < 3); nlinarith)
  have hapos : 0 < 1-a := sub_pos.mpr ha1
  have hZ : (1-a)⁻¹ ≤ Z t := by
    have h := tsum_comp_le_tsum_of_inj (z_summable ht) (z_nonneg t)
      ((pow_right_strictMono₀ (by norm_num : 1 < (3 : ℕ))).injective)
    simp only [Function.comp_def, z_prime_powers] at h
    rw [tsum_geometric_of_abs_lt_one (by rw [abs_of_pos ha0]; exact ha1)] at h
    exact h
  have hZ0 : 0 < Z t := zero_lt_one.trans_le (Z_one_le ht)
  have hE : E t = (Z t)⁻¹ := by
    have h := ze_inverse ht
    apply (mul_left_cancel₀ hZ0.ne')
    rw [h, mul_inv_cancel₀ hZ0.ne']
  have hi : E t ≤ 1-a := by
    rw [hE]
    have h := inv_anti₀ (by positivity : 0 < (1-a)⁻¹) hZ
    simpa only [inv_inv] using h
  have haeq : a = Real.exp (-t*Real.log 3)/3 := by
    dsimp [a]
    rw [show -(1+t)*Real.log 3 = -t*Real.log 3+-Real.log 3 by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    ring
  rw [haeq] at hi
  linarith

private lemma ecoeff_exp (t : ℝ) (n : ℕ) :
    ecoeff t n = if Odd n then
      (ArithmeticFunction.moebius n : ℝ)/(n : ℝ)*Real.exp (-t*Real.log n) else 0 := by
  classical
  unfold ecoeff zcoeff
  split_ifs with ho
  · have hn : 0 < (n : ℝ) := by exact_mod_cast ho.pos
    rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ n),
      show -(1+t) = -t+-1 by ring, Real.rpow_add hn,
      Real.rpow_neg_one, Real.rpow_def_of_pos hn]
    rw [show Real.log (n : ℝ) * -t = -t*Real.log n by ring]
    ring
  · simp

private lemma S_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => S N t) atTop (𝓝 (E t-1)) := by
  classical
  have hlim := ((e_summable ht).hasSum.tendsto_sum_nat).sub_const 1
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
  have hs : (∑ n ∈ Finset.range N, ecoeff t n) = 1+S N t := by
    rw [show Finset.range N = Finset.range 3 ∪ Finset.Ico 3 N by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega) hN],
      Finset.sum_union (by apply Finset.disjoint_left.mpr; intro n hn hm; simp_all; omega)]
    have hhead : (∑ n ∈ Finset.range 3, ecoeff t n) = 1 := by
      norm_num [ecoeff, zcoeff, Finset.sum_range_succ]
    rw [hhead]
    congr 1
    simp only [S, Finset.sum_filter, ecoeff_exp]
    rw [show Finset.range N = Finset.range 3 ∪ Finset.Ico 3 N by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega) hN],
      Finset.sum_union (by apply Finset.disjoint_left.mpr; intro n hn hm; simp_all; omega)]
    have hz : (∑ n ∈ Finset.range 3,
        if Odd n ∧ 3 ≤ n then (ArithmeticFunction.moebius n : ℝ)/(n : ℝ)*
          Real.exp (-t*Real.log n) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hn3 : ¬3 ≤ n := by have := Finset.mem_range.mp hn; omega
      simp [hn3]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro n hn
    have hn3 := (Finset.mem_Ico.mp hn).1
    simp [hn3]
  rw [hs]
  ring

private def majorant (t : ℝ) : ℝ := 6*(1+t)*Real.exp (-(Real.log 3*t))

private lemma majorant_integrable : IntegrableOn majorant (Ioi (0 : ℝ)) := by
  have hl : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  apply (((gamma_integrable hl 0).add (gamma_integrable hl 1)).const_mul 6).congr
  filter_upwards with t
  dsimp [majorant]
  ring

private lemma prefix_measurable (N : ℕ) :
    AEStronglyMeasurable (fun t => nu t*S N t) (volume.restrict (Ioi (0 : ℝ))) := by
  classical
  have hm : Measurable (S N) := by
    unfold S
    fun_prop
  exact nu_measurable.mul hm.aestronglyMeasurable

private lemma prefix_bound (N : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖nu t*S N t‖ ≤ majorant t := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (nu_bounds ht).1]
  calc
    _ ≤ (2*(1+t))*(3*Real.exp (-t*Real.log 3)) := by
      apply mul_le_mul (nu_bounds ht).2 (S_bound N ht) (abs_nonneg _) (by positivity)
    _ = _ := by
      dsimp [majorant]
      rw [show -(Real.log (3 : ℝ)*t) = -t*Real.log 3 by ring]
      ring

private lemma natural_dct :
    IntegrableOn (fun t => nu t*(E t-1)) (Ioi (0 : ℝ)) ∧
    Tendsto naturalPrefix atTop (𝓝 (∫ t in Ioi (0 : ℝ), nu t*(E t-1))) := by
  have hlim : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun N : ℕ => nu t*S N t) atTop (𝓝 (nu t*(E t-1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (S_tendsto ht).const_mul (nu t)
  have hbound : ∀ N : ℕ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖nu t*S N t‖ ≤ majorant t := fun N =>
    ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => prefix_bound N ht)
  have hf : AEStronglyMeasurable (fun t => nu t*(E t-1))
      (volume.restrict (Ioi (0 : ℝ))) :=
    aestronglyMeasurable_of_tendsto_ae atTop prefix_measurable hlim
  have hi : IntegrableOn (fun t => nu t*(E t-1)) (Ioi (0 : ℝ)) := by
    apply majorant_integrable.mono' hf
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact le_of_tendsto ((S_tendsto ht).const_mul (nu t)).norm
      (Eventually.of_forall (fun N => prefix_bound N ht))
  refine ⟨hi, ?_⟩
  have hdct := tendsto_integral_of_dominated_convergence majorant
    prefix_measurable majorant_integrable hbound hlim
  simpa only [← prefix_integral] using hdct

/-- The full odd high q-component has its ordinary natural limit and a strict
negative margin from the genuine prime 3. The unit, low part, clipping boundaries,
finite terminal correction and pressure are separate obligations in full Robin. -/
theorem result :
    ∃ Q : ℝ, Tendsto naturalPrefix atTop (𝓝 Q) ∧
      Q ≤ -q (Real.log 3)/3 ∧ -q (Real.log 3)/3 < 0 := by
  have hl : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hdct := natural_dct
  obtain ⟨Q, hQ⟩ := ActualFactorialRobinHighWeight.result.2.2.2.2.2
  have heq : Q = ∫ t in Ioi (0 : ℝ), nu t*(E t-1) :=
    tendsto_nhds_unique hQ hdct.2
  refine ⟨Q, hQ, ?_, ?_⟩
  · rw [heq]
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ), -(nu t*Real.exp (-(Real.log 3*t)))/3 := by
        apply integral_mono_ae hdct.1 ((q_laplace hl).1.neg.div_const 3)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        dsimp only [Pi.neg_apply]
        have hm := mul_le_mul_of_nonneg_left (E_margin ht) (nu_bounds ht).1.le
        rw [show -t*Real.log (3 : ℝ) = -(Real.log 3*t) by ring] at hm
        nlinarith
      _ = -q (Real.log 3)/3 := by
        rw [integral_div, integral_neg, ← (q_laplace hl).2]
  · have hp := (ActualFactorialRobinHighWeight.result.1 (Real.log 3) hl).1
    linarith

end D5.S3.Arith.Robin.ActualFactorialRobinHighSign
#print axioms D5.S3.Arith.Robin.ActualFactorialRobinHighSign.result
