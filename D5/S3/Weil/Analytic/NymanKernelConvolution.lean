/- GID: D5/S3/Weil/Analytic/NymanKernelConvolution
   generality: I
   mirror-B: none(waiver:nyman-signed-prime-support)
   mirror-E: none(waiver:nyman-signed-prime)
   anchors: []
   utility: none
   digest: The fixed Nyman kernel is the convolution of four exponential boxes in logarithmic coordinates. -/

import D5.S3.Weil.Analytic.NymanFixedRationalKernel
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Pointwise logarithmic convolution for the fixed Nyman kernel.
This draft has been checked against the source signatures and awaits Lean elaboration. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators Convolution

namespace NymanKernelConvolution

open NymanFixedRationalKernel (A A_pos b c one_lt_A)

/-- The logarithmic width of a single factor. -/
def h : ℝ := Real.log A

theorem h_eq_log_seven_sixths : h = Real.log (7 / 6 : ℝ) := rfl

theorem h_pos : 0 < h := Real.log_pos one_lt_A

theorem exp_h : Real.exp h = A := Real.exp_log A_pos

/-- The half-line exponential with integral rate `j`. -/
def P (j : ℕ) : ℝ → ℝ := (Ioi (0 : ℝ)).indicator fun t => Real.exp ((j : ℝ) * t)

/-- The restriction of `P j` to `(0, h]`. -/
def q (j : ℕ) : ℝ → ℝ := (Ioc (0 : ℝ) h).indicator fun t => Real.exp ((j : ℝ) * t)

/-- Translation to the right by `a`. -/
def shift (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => f (t - a)

/-- The difference `f - w * shift a f`. -/
def difference (a w : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => f t - w * shift a f t

theorem q_eq_difference_exp (j : ℕ) :
    q j = difference h (Real.exp ((j : ℝ) * h)) (P j) := by
  funext t
  have hfactor : Real.exp ((j : ℝ) * h) * Real.exp ((j : ℝ) * (t - h)) =
      Real.exp ((j : ℝ) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  by_cases ht : 0 < t
  · by_cases hle : t ≤ h
    · have harg : ¬ 0 < t - h := not_lt.mpr (sub_nonpos.mpr hle)
      simp [q, P, difference, shift, indicator, mem_Ioc, mem_Ioi, ht, hle, harg]
    · have harg : 0 < t - h := sub_pos.mpr (lt_of_not_ge hle)
      simp [q, P, difference, shift, indicator, mem_Ioc, mem_Ioi, ht, hle, harg, hfactor]
  · have harg : ¬ 0 < t - h :=
      not_lt.mpr (sub_nonpos.mpr ((le_of_not_gt ht).trans h_pos.le))
    simp [q, P, difference, shift, indicator, mem_Ioc, mem_Ioi, ht, harg]

/-- The formula for a convolution of `r + 1` half-line exponentials. -/
def positivePower (r : ℕ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator fun t => (Real.exp t - 1) ^ r / (r.factorial : ℝ)

/-- The left-associated convolution of rates `0` through `r`. -/
def prefixConvolution : ℕ → ℝ → ℝ
  | 0 => P 0
  | r + 1 => prefixConvolution r ⋆ P (r + 1)

private theorem convolution_comm_real (f g : ℝ → ℝ) : f ⋆ g = g ⋆ f := by
  funext t
  rw [convolution_lsmul_swap (f := f) (g := g), convolution_lsmul (f := g) (g := f)]
  simp only [smul_eq_mul, mul_comm]

private theorem positivePower_zero : positivePower 0 = P 0 := by
  funext t
  simp [positivePower, P, indicator]

/-- Add the exponential of rate `r + 1`. The substitution `u = exp v` turns
  the convolution slice into the integral of `(exp t - u)^r / r!`. -/
theorem positivePower_succ (r : ℕ) :
    positivePower r ⋆ P (r + 1) = positivePower (r + 1) := by
  let f : ℝ → ℝ := fun v => Real.exp (((r + 1 : ℕ) : ℝ) * v)
  let g : ℝ → ℝ := fun v => (Real.exp v - 1) ^ r / (r.factorial : ℝ)
  rw [convolution_comm_real]
  change (Ioi (0 : ℝ)).indicator f ⋆ (Ioi (0 : ℝ)).indicator g = _
  rw [← posConvolution_eq_convolution_indicator f g (ContinuousLinearMap.lsmul ℝ ℝ) volume]
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have ht' : 0 < t := ht
    simp only [posConvolution, positivePower, indicator_of_mem ht]
    change (∫ v in (0 : ℝ)..t, f v * g (t - v)) =
      (Real.exp t - 1) ^ (r + 1) / ((r + 1).factorial : ℝ)
    calc
      _ = ∫ v in (0 : ℝ)..t,
          ((Real.exp t - Real.exp v) ^ r * Real.exp v) / (r.factorial : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht'.le
        intro v _
        change Real.exp (((r + 1 : ℕ) : ℝ) * v) *
          ((Real.exp (t - v) - 1) ^ r / (r.factorial : ℝ)) =
          (Real.exp t - Real.exp v) ^ r * Real.exp v / (r.factorial : ℝ)
        rw [Real.exp_nat_mul v (r + 1), Real.exp_sub, pow_succ (Real.exp v) r]
        have hp : ((Real.exp t / Real.exp v - 1) * Real.exp v) ^ r =
            (Real.exp t - Real.exp v) ^ r := by
          rw [sub_mul, div_mul_cancel₀ _ (Real.exp_pos v).ne', one_mul]
        rw [← hp, mul_pow]
        ring
      _ = ∫ u in Real.exp 0..Real.exp t, (Real.exp t - u) ^ r / (r.factorial : ℝ) := by
        simpa only [Function.comp_apply, div_mul_eq_mul_div₀] using
          (intervalIntegral.integral_comp_mul_deriv
            (a := 0) (b := t) (f := Real.exp) (f' := Real.exp)
            (g := fun u : ℝ => (Real.exp t - u) ^ r / (r.factorial : ℝ))
            (fun v _ => Real.hasDerivAt_exp v)
            Real.continuous_exp.continuousOn (by fun_prop))
      _ = ∫ w in (0 : ℝ)..(Real.exp t - 1), w ^ r / (r.factorial : ℝ) := by
        simpa only [Real.exp_zero, sub_self] using
          (intervalIntegral.integral_comp_sub_left (a := Real.exp 0) (b := Real.exp t)
            (fun w : ℝ => w ^ r / (r.factorial : ℝ)) (Real.exp t))
      _ = _ := by
        have hz : (0 : ℝ) ^ (r + 1) = 0 := zero_pow (Nat.succ_ne_zero r)
        simp only [intervalIntegral.integral_div, integral_pow,
          hz, sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
          Nat.cast_add, Nat.cast_one, div_div]
  · simp only [posConvolution, positivePower, indicator_of_notMem ht]

/-- The convolution of `P 0, …, P r` on all of `ℝ`, with its value at zero specified. -/
theorem prefixConvolution_eq_positivePower (r : ℕ) : prefixConvolution r = positivePower r := by
  induction r with
  | zero => exact positivePower_zero.symm
  | succ r ih =>
    change prefixConvolution r ⋆ P (r + 1) = positivePower (r + 1)
    rw [ih, positivePower_succ]

theorem prefixConvolution_apply_of_pos (r : ℕ) {t : ℝ} (ht : 0 < t) :
    prefixConvolution r t = (Real.exp t - 1) ^ r / (r.factorial : ℝ) := by
  rw [prefixConvolution_eq_positivePower, positivePower, indicator_of_mem (mem_Ioi.mpr ht)]

/-- The hypotheses needed for absolute integrability of every convolution slice. -/
private structure CausalBounded (f : ℝ → ℝ) : Prop where
  measurable : Measurable f
  zero_of_nonpos : ∀ x ≤ 0, f x = 0
  bounded : ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ≤ x, ‖f y‖ ≤ C

private theorem causalBounded_indicator {f : ℝ → ℝ} (hf : Continuous f) :
    CausalBounded ((Ioi (0 : ℝ)).indicator f) := by
  refine ⟨hf.measurable.indicator measurableSet_Ioi, ?_, ?_⟩
  · intro x hx
    exact indicator_of_notMem (notMem_Ioi.mpr hx) f
  · intro x
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) x)).exists_bound_of_continuousOn
      hf.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro y hy
    by_cases hy₀ : y ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hy₀]
      exact (hC y ⟨(mem_Ioi.mp hy₀).le, hy⟩).trans (le_max_left _ _)
    · rw [indicator_of_notMem hy₀, norm_zero]
      exact le_max_right _ _

private theorem CausalBounded.difference {f : ℝ → ℝ} (hf : CausalBounded f)
    {a : ℝ} (ha : 0 ≤ a) (w : ℝ) : CausalBounded (difference a w f) := by
  refine ⟨?_, ?_, ?_⟩
  · change Measurable (fun x : ℝ => f x - w * f (x - a))
    exact hf.measurable.sub (measurable_const.mul (hf.measurable.comp (measurable_id.sub_const a)))
  · intro x hx
    change f x - w * f (x - a) = 0
    rw [hf.zero_of_nonpos x hx, hf.zero_of_nonpos (x - a) ((sub_le_self x ha).trans hx),
      mul_zero, sub_zero]
  · intro x
    obtain ⟨C, hC₀, hC⟩ := hf.bounded x
    refine ⟨C + ‖w‖ * C, add_nonneg hC₀ (mul_nonneg (norm_nonneg _) hC₀), ?_⟩
    intro y hy
    calc
      _ ≤ ‖f y‖ + ‖w * f (y - a)‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_mul]
        exact add_le_add (hC y hy)
          (mul_le_mul_of_nonneg_left (hC (y - a) ((sub_le_self y ha).trans hy)) (norm_nonneg _))

private theorem CausalBounded.integrable_slice {f g : ℝ → ℝ} (hf : CausalBounded f)
    (hg : CausalBounded g) (t : ℝ) : Integrable (fun v : ℝ => f v * g (t - v)) := by
  let F : ℝ → ℝ := fun v => f v * g (t - v)
  have hm : Measurable F := hf.measurable.mul (hg.measurable.comp (measurable_id.const_sub t))
  obtain ⟨Cf, hCf₀, hCf⟩ := hf.bounded t
  obtain ⟨Cg, _, hCg⟩ := hg.bounded t
  have hI : IntegrableOn F (Ioo (0 : ℝ) t) := by
    refine IntegrableOn.of_bound measure_Ioo_lt_top hm.aestronglyMeasurable (Cf * Cg) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall ?_)
    intro v hv
    change ‖f v * g (t - v)‖ ≤ Cf * Cg
    rw [norm_mul]
    exact mul_le_mul (hCf v hv.2.le) (hCg (t - v) (sub_le_self t hv.1.le)) (norm_nonneg _) hCf₀
  have hF : (Ioo (0 : ℝ) t).indicator F = F := by
    funext v
    by_cases hv : v ∈ Ioo (0 : ℝ) t
    · exact indicator_of_mem hv F
    · rw [indicator_of_notMem hv]
      change 0 = f v * g (t - v)
      by_cases hv₀ : 0 < v
      · have htv : t ≤ v := le_of_not_gt fun hvt => hv ⟨hv₀, hvt⟩
        rw [hg.zero_of_nonpos (t - v) (sub_nonpos.mpr htv), mul_zero]
      · rw [hf.zero_of_nonpos v (le_of_not_gt hv₀), zero_mul]
  change Integrable F
  rw [← hF]
  exact hI.integrable_indicator measurableSet_Ioo

private theorem convolution_difference_right {f g : ℝ → ℝ} (hf : CausalBounded f)
    (hg : CausalBounded g) (a w : ℝ) :
    f ⋆ difference a w g = difference a w (f ⋆ g) := by
  funext t
  change (∫ v : ℝ, f v * (g (t - v) - w * g (t - v - a))) =
    (∫ v : ℝ, f v * g (t - v)) - w * (∫ v : ℝ, f v * g (t - a - v))
  calc
    _ = ∫ v : ℝ, f v * g (t - v) - w * (f v * g (t - a - v)) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun v => ?_
      dsimp only
      rw [show t - v - a = t - a - v by ring]
      ring
    _ = _ := by
      rw [integral_sub (hf.integrable_slice hg t) ((hf.integrable_slice hg (t - a)).const_mul w),
        integral_const_mul]

private theorem convolution_difference_left {f g : ℝ → ℝ} (hf : CausalBounded f)
    (hg : CausalBounded g) (a w : ℝ) :
    difference a w f ⋆ g = difference a w (f ⋆ g) := by
  rw [convolution_comm_real (difference a w f) g, convolution_difference_right hg hf,
    convolution_comm_real g f]

private def D (j : ℕ) : (ℝ → ℝ) → ℝ → ℝ := difference h (A ^ j)

private theorem q_eq_D (j : ℕ) : q j = D j (P j) := by
  simpa only [D, Real.exp_nat_mul, exp_h] using q_eq_difference_exp j

private theorem CausalBounded.D {f : ℝ → ℝ} (hf : CausalBounded f) (j : ℕ) :
    CausalBounded (D j f) := hf.difference h_pos.le (A ^ j)

private theorem convolution_D_left {f g : ℝ → ℝ} (hf : CausalBounded f)
    (hg : CausalBounded g) (j : ℕ) : D j f ⋆ g = D j (f ⋆ g) :=
  convolution_difference_left hf hg h (A ^ j)

private theorem convolution_D_right {f g : ℝ → ℝ} (hf : CausalBounded f)
    (hg : CausalBounded g) (j : ℕ) : f ⋆ D j g = D j (f ⋆ g) :=
  convolution_difference_right hf hg h (A ^ j)

private theorem fourfold_q_eq_differences :
    ((q 0 ⋆ q 1) ⋆ q 2) ⋆ q 3 = D 3 (D 2 (D 1 (D 0 (positivePower 3)))) := by
  have hP (j : ℕ) : CausalBounded (P j) := by
    unfold P
    exact causalBounded_indicator (by fun_prop)
  have hpow (r : ℕ) : CausalBounded (positivePower r) := by
    unfold positivePower
    exact causalBounded_indicator (by fun_prop)
  have first : q 0 ⋆ q 1 = D 1 (D 0 (positivePower 1)) := by
    rw [q_eq_D 0, q_eq_D 1, convolution_D_right ((hP 0).D 0) (hP 1) 1,
      convolution_D_left (hP 0) (hP 1) 0, ← positivePower_zero, positivePower_succ 0]
  have second : (q 0 ⋆ q 1) ⋆ q 2 = D 2 (D 1 (D 0 (positivePower 2))) := by
    rw [first, q_eq_D 2, convolution_D_right (((hpow 1).D 0).D 1) (hP 2) 2,
      convolution_D_left ((hpow 1).D 0) (hP 2) 1, convolution_D_left (hpow 1) (hP 2) 0,
      positivePower_succ 1]
  rw [second, q_eq_D 3, convolution_D_right ((((hpow 2).D 0).D 1).D 2) (hP 3) 3,
    convolution_D_left (((hpow 2).D 0).D 1) (hP 3) 2,
    convolution_D_left ((hpow 2).D 0) (hP 3) 1, convolution_D_left (hpow 2) (hP 3) 0,
    positivePower_succ 2]

/-- The four differences expanded for an arbitrary function and step. -/
theorem four_differences (a d : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    difference d (a ^ 3) (difference d (a ^ 2) (difference d a (difference d 1 f))) t =
      f t - (1 + a + a ^ 2 + a ^ 3) * f (t - d) +
        (a + a ^ 2 + 2 * a ^ 3 + a ^ 4 + a ^ 5) * f (t - 2 * d) -
        (a ^ 3 + a ^ 4 + a ^ 5 + a ^ 6) * f (t - 3 * d) + a ^ 6 * f (t - 4 * d) := by
  have h₂ (x : ℝ) : x - d - d = x - 2 * d := by ring
  have h₃ (x : ℝ) : x - 2 * d - d = x - 3 * d := by ring
  have h₄ (x : ℝ) : x - 3 * d - d = x - 4 * d := by ring
  simp only [difference, shift, h₂, h₃, h₄]
  ring

private theorem positivePower_three (t : ℝ) :
    positivePower 3 t = (max (Real.exp t - 1) 0) ^ 3 / 6 := by
  by_cases ht : 0 < t
  · have he : 1 ≤ Real.exp t := by simpa only [Real.exp_zero] using Real.exp_monotone ht.le
    norm_num [positivePower, indicator, mem_Ioi, ht, max_eq_left (sub_nonneg.mpr he),
      Nat.factorial_succ]
  · have he : Real.exp t ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_monotone (le_of_not_gt ht)
    norm_num [positivePower, indicator, mem_Ioi, ht, max_eq_right (sub_nonpos.mpr he)]

private theorem positivePower_three_shift (t : ℝ) (k : ℕ) :
    positivePower 3 (t - (k : ℝ) * h) = (max (Real.exp t / A ^ k - 1) 0) ^ 3 / 6 := by
  rw [positivePower_three, Real.exp_sub, Real.exp_nat_mul h k, exp_h]

/-- The exact pointwise identity, including all knots and both endpoints. -/
theorem b_exp_eq_fourfold_convolution (t : ℝ) :
    b (Real.exp t) = (((q 0 ⋆ q 1) ⋆ q 2) ⋆ q 3) t := by
  rw [fourfold_q_eq_differences]
  change b (Real.exp t) =
    difference h (A ^ 3) (difference h (A ^ 2) (difference h (A ^ 1)
      (difference h (A ^ 0) (positivePower 3)))) t
  rw [pow_zero, pow_one, four_differences A h]
  have h₁ := positivePower_three_shift t 1
  have h₂ := positivePower_three_shift t 2
  have h₃ := positivePower_three_shift t 3
  have h₄ := positivePower_three_shift t 4
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul] at h₁ h₂ h₃ h₄
  rw [positivePower_three t, h₁, h₂, h₃, h₄]
  simp [b, c, Fin.sum_univ_succ]
  <;> ring

end NymanKernelConvolution
