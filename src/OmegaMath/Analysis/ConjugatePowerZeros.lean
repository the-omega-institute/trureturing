import OmegaBuild.Commands
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
Omega original.

Equal-amplitude powers of the two affine factors centered at the imaginary
unit have only real zeros. The argument compares their norms, without
enumerating their roots.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Omega

/-- A balanced sum of positive powers of `1 + I*z` and `1 - I*z`
can vanish only on the real axis. -/
theorem conjugate_power_sum_root_real (a b z : ℂ) (d : ℕ)
    (ha : a ≠ 0) (hab : ‖a‖ = ‖b‖) (hd : d ≠ 0)
    (hz : a * (1 + Complex.I * z) ^ d + b * (1 - Complex.I * z) ^ d = 0) :
    z.im = 0 := by
  have heq : a * (1 + Complex.I * z) ^ d =
      -(b * (1 - Complex.I * z) ^ d) := eq_neg_of_add_eq_zero_left hz
  have hn := congrArg norm heq
  simp only [norm_mul, norm_pow, norm_neg] at hn
  rw [← hab] at hn
  have hp := mul_left_cancel₀ (norm_pos_iff.mpr ha).ne' hn
  have he := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd).mp hp
  have hs := congrArg (fun r : ℝ => r ^ 2) he
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
    Complex.add_im, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, sub_zero, zero_add, add_zero] at hs
  nlinarith

end Omega
