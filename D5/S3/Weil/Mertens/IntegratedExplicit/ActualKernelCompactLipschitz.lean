/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCompactLipschitz
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCompactLipschitz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit arithmetic Lipschitz control through every prime-power ramp corner. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set
open scoped BigOperators
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz

/-- The exact finite reciprocal Mangoldt mass. -/
def A (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n / (n : ℝ)

/-- The exact finite Mangoldt mass. -/
def P (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n

/-- A constant valid on the closed positive window, including all arithmetic corners. -/
def L (a b : ℝ) (N : ℕ) : ℝ :=
  (Real.exp (b / 2) * (A N + |Real.eulerMascheroniConstant - 1| + b) + P N +
    |Real.log (2 * Real.pi)| + 1 + |Real.log (1 - Real.exp (-(2 * a)))|) / 2

private def ramp (n : ℕ) (t : ℝ) : ℝ :=
  max (Real.exp (t / 2) / (n : ℝ) - Real.exp (-t / 2)) 0

private def smooth (t : ℝ) : ℝ :=
  (1 + Real.eulerMascheroniConstant - t) * Real.exp (t / 2) -
    Real.log (2 * Real.pi) * Real.exp (-t / 2) + Real.exp (-t / 2) * trivialT t

private lemma damped_ramp (n : ℕ) (t : ℝ) :
    Real.exp (-t / 2) * mangoldtRamp n (Real.exp t) =
      ArithmeticFunction.vonMangoldt n * ramp n t := by
  have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold mangoldtRamp ramp
  rw [mul_left_comm, mul_max_of_nonneg _ _ (Real.exp_nonneg _), mul_zero]
  congr 2
  rw [mul_sub, ← mul_div_assoc, he, mul_one]

private lemma finite_decomposition {t b : ℝ} {N : ℕ} (ht : 0 ≤ t)
    (htb : t ≤ b) (hN : Real.exp b < N) :
    K t = (∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * ramp n t) + smooth t := by
  rw [K, abs_of_nonneg ht, U_eq_complete_ramps (Real.exp_nonneg _),
    mangoldtPart_eq_range (Real.exp_nonneg _) ((Real.exp_le_exp.mpr htb).trans_lt hN),
    Real.log_exp]
  have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hs : Real.exp (-t / 2) * (∑ n ∈ Finset.range N, mangoldtRamp n (Real.exp t)) =
      ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * ramp n t := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => damped_ramp n t)
  dsimp only [smooth]
  calc
    _ = Real.exp (-t / 2) * (∑ n ∈ Finset.range N, mangoldtRamp n (Real.exp t)) +
        (1 + Real.eulerMascheroniConstant - t) * (Real.exp (-t / 2) * Real.exp t) -
        Real.log (2 * Real.pi) * Real.exp (-t / 2) + Real.exp (-t / 2) * trivialT t := by ring
    _ = _ := by rw [hs, he]; ring

private lemma ramp_bound {a b u v : ℝ} (ha : 0 ≤ a) (hu : u ∈ Icc a b)
    (hv : v ∈ Icc a b) (n : ℕ) :
    |ramp n u - ramp n v| ≤ (Real.exp (b / 2) / (n : ℝ) + 1) / 2 * |u - v| := by
  have hd (t : ℝ) : HasDerivAt
      (fun w : ℝ => Real.exp (w / 2) / (n : ℝ) - Real.exp (-w / 2))
      ((Real.exp (t / 2) / (n : ℝ) + Real.exp (-t / 2)) / 2) t := by
    convert ((((hasDerivAt_id t).div_const 2).exp).div_const (n : ℝ)).sub
      (((hasDerivAt_id t).neg.div_const 2).exp) using 1 <;> dsimp <;> ring
  have hb (t : ℝ) (ht : t ∈ Icc a b) :
      ‖(Real.exp (t / 2) / (n : ℝ) + Real.exp (-t / 2)) / 2‖ ≤
        (Real.exp (b / 2) / (n : ℝ) + 1) / 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have he := div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (show t / 2 ≤ b / 2 by linarith [ht.2])) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hm : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
    linarith
  exact (abs_max_sub_max_le_abs _ _ 0).trans (by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t (_ : t ∈ Icc a b) => (hd t).hasDerivWithinAt) hb (convex_Icc a b) hv hu)

private lemma smooth_derivative {t : ℝ} (ht : 0 < t) : HasDerivAt smooth
    ((Real.exp (t / 2) * (Real.eulerMascheroniConstant - 1 - t) +
      Real.log (2 * Real.pi) * Real.exp (-t / 2) +
      Real.exp (-t / 2) * (trivialT t + Real.log (1 - Real.exp (-(2 * t))))) / 2) t := by
  convert (((hasDerivAt_const t (1 + Real.eulerMascheroniConstant)).sub
    (hasDerivAt_id t)).mul (((hasDerivAt_id t).div_const 2).exp) |>.sub
      ((((hasDerivAt_id t).neg.div_const 2).exp).const_mul (Real.log (2 * Real.pi))) |>.add
        ((((hasDerivAt_id t).neg.div_const 2).exp).mul (trivialT_derivative ht)) using 1
  · rfl
  · dsimp; ring

private lemma smooth_bound {a b u v : ℝ} (ha : 0 < a) (hu : u ∈ Icc a b)
    (hv : v ∈ Icc a b) :
    |smooth u - smooth v| ≤
      (Real.exp (b / 2) * (|Real.eulerMascheroniConstant - 1| + b) +
        |Real.log (2 * Real.pi)| + 1 + |Real.log (1 - Real.exp (-(2 * a)))|) / 2 * |u - v| := by
  have hb (t : ℝ) (ht : t ∈ Icc a b) :
      ‖(Real.exp (t / 2) * (Real.eulerMascheroniConstant - 1 - t) +
        Real.log (2 * Real.pi) * Real.exp (-t / 2) +
        Real.exp (-t / 2) * (trivialT t + Real.log (1 - Real.exp (-(2 * t))))) / 2‖ ≤
      (Real.exp (b / 2) * (|Real.eulerMascheroniConstant - 1| + b) +
        |Real.log (2 * Real.pi)| + 1 + |Real.log (1 - Real.exp (-(2 * a)))|) / 2 := by
    have ht0 : 0 < t := ha.trans_le ht.1
    have hm : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hp : Real.exp (t / 2) ≤ Real.exp (b / 2) := Real.exp_le_exp.mpr (by linarith [ht.2])
    have hg : |Real.eulerMascheroniConstant - 1 - t| ≤ |Real.eulerMascheroniConstant - 1| + b :=
      (abs_sub _ _).trans (by rw [abs_of_pos ht0]; linarith [ht.2])
    have hT : |trivialT t| ≤ 1 := by
      rw [abs_of_nonneg (trivialT_nonneg ht0.le)]
      linarith [trivialT_le_mass ht0.le, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have harg : 0 < 1 - Real.exp (-(2 * a)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    have hlog : |Real.log (1 - Real.exp (-(2 * t)))| ≤
        |Real.log (1 - Real.exp (-(2 * a)))| := by
      have hneg : Real.log (1 - Real.exp (-(2 * t))) ≤ 0 :=
        Real.log_nonpos (by linarith [Real.exp_le_one_iff.mpr (show -(2 * t) ≤ 0 by linarith)])
          (by linarith [Real.exp_pos (-(2 * t))])
      have hle : Real.log (1 - Real.exp (-(2 * a))) ≤ Real.log (1 - Real.exp (-(2 * t))) :=
        Real.log_le_log harg (by linarith [Real.exp_le_exp.mpr
          (show -(2 * t) ≤ -(2 * a) by linarith [ht.1])])
      rw [abs_of_nonpos hneg, abs_of_nonpos (hle.trans hneg)]
      linarith
    have h₁ := mul_le_mul hp hg (abs_nonneg _) (Real.exp_nonneg _)
    have h₂ := mul_le_mul_of_nonneg_left hm (abs_nonneg (Real.log (2 * Real.pi)))
    have h₃ := mul_le_mul hm ((abs_add _ _).trans (add_le_add hT hlog))
      (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ ≤ |Real.exp (t / 2) * (Real.eulerMascheroniConstant - 1 - t)| +
          |Real.log (2 * Real.pi) * Real.exp (-t / 2)| +
          |Real.exp (-t / 2) * (trivialT t + Real.log (1 - Real.exp (-(2 * t))))| :=
        (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
      _ ≤ _ := by
        simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
        simpa only [one_mul, mul_one, add_assoc] using add_le_add (add_le_add h₁ h₂) h₃
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (ht : t ∈ Icc a b) => (smooth_derivative (ha.trans_le ht.1)).hasDerivWithinAt)
    hb (convex_Icc a b) hv hu

/-- Exact arithmetic compact Lipschitz control, with no differentiability hypothesis at corners. -/
theorem kernel_lipschitz {a b : ℝ} {N : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hN : Real.exp b < N) {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    |K u - K v| ≤ L a b N * |u - v| := by
  have hs : |(∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * ramp n u) -
      (∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * ramp n v)| ≤
      ((Real.exp (b / 2) * A N + P N) / 2) * |u - v| := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.range N, |ArithmeticFunction.vonMangoldt n * ramp n u -
          ArithmeticFunction.vonMangoldt n * ramp n v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n *
          ((Real.exp (b / 2) / (n : ℝ) + 1) / 2 * |u - v|) := by
        apply Finset.sum_le_sum
        intro n _
        rw [← mul_sub, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_left (ramp_bound ha.le hu hv n) ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by
        calc
          _ = ∑ n ∈ Finset.range N,
              ((Real.exp (b / 2) * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
                ArithmeticFunction.vonMangoldt n) / 2) * |u - v| := by
            apply Finset.sum_congr rfl
            intro n _
            ring
          _ = _ := by
            rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
            rfl
  rw [finite_decomposition (ha.le.trans hu.1) hu.2 hN,
    finite_decomposition (ha.le.trans hv.1) hv.2 hN]
  calc
    _ ≤ |(∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * ramp n u) -
        (∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * ramp n v)| +
        |smooth u - smooth v| := by convert abs_add _ _ using 1 <;> congr 1 <;> ring
    _ ≤ _ := (add_le_add hs (smooth_bound ha hu hv)).trans (by dsimp [L]; nlinarith)

#print axioms kernel_lipschitz

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz
