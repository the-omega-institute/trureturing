import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

namespace D5.S3.Analytic.NativeHalfPowerLip

open Complex

private theorem log_lip_pos {z : ℂ} (hz : 0 < z.im) :
    log z = log (-z) + (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re, norm_neg, mul_re]
  · simp [log_im, arg_neg_eq_arg_sub_pi_of_im_pos hz, mul_im]

private theorem log_lip_neg {z : ℂ} (hz : z.im < 0) :
    log z = log (-z) - (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re, norm_neg, mul_re]
  · simp [log_im, arg_neg_eq_arg_add_pi_of_im_neg hz, mul_im]

/-- The inverse square root across the upper lip of the negative real cut. -/
theorem invHalfPower_upper {z : ℂ} (hz : 0 < z.im) :
    z ^ (-1 / 2 : ℂ) = (-I) * (-z) ^ (-1 / 2 : ℂ) := by
  have hn : z ≠ 0 := fun he => hz.ne' (by simp [he])
  have hI : exp (((Real.pi : ℂ) * I) * (-1 / 2 : ℂ)) = -I := by
    rw [show (Real.pi : ℂ) * I * (-1 / 2 : ℂ) = -(Real.pi : ℂ) / 2 * I by ring,
      exp_neg_pi_div_two_mul_I]
  rw [cpow_def_of_ne_zero hn, cpow_def_of_ne_zero (neg_ne_zero.mpr hn),
    log_lip_pos hz, add_mul, exp_add, hI, mul_comm]

/-- The inverse square root across the lower lip of the negative real cut. -/
theorem invHalfPower_lower {z : ℂ} (hz : z.im < 0) :
    z ^ (-1 / 2 : ℂ) = I * (-z) ^ (-1 / 2 : ℂ) := by
  have hn : z ≠ 0 := fun he => hz.ne (by simp [he])
  have hI : exp (-(((Real.pi : ℂ) * I) * (-1 / 2 : ℂ))) = I := by
    rw [show -((Real.pi : ℂ) * I * (-1 / 2 : ℂ)) = (Real.pi : ℂ) / 2 * I by ring,
      exp_pi_div_two_mul_I]
  rw [cpow_def_of_ne_zero hn, cpow_def_of_ne_zero (neg_ne_zero.mpr hn),
    log_lip_neg hz, sub_mul, sub_eq_add_neg, exp_add, hI, mul_comm]

#print axioms invHalfPower_upper
#print axioms invHalfPower_lower

end D5.S3.Analytic.NativeHalfPowerLip
