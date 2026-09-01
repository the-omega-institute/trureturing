/- GID: D5/S3/Weil/TestFunctions/StickyTailCompletionError
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/StickyTailCompletionError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A uniform Herglotz-kernel derivative bound controls sticky-tail completion. -/

import D5.S3.Weil.Budget.CaratheodoryScaleCovariance
import Mathlib.Analysis.Calculus.Deriv.Inv

/- Library-search audit trail (2026-09-01):
   * The target atom has no receipt, occurs once in residual-open with empty
     coverage, and has no absorbed-closed entry. Sticky-tail spellings have no
     D5 declaration hit; the adjacent source theorems 305.1 and 305.2 are open.
   * D5 already owns `caratheodoryKernel`. Its nearby norm and derivative
     lemmas are private, and the derivative varies the observer variable rather
     than the spectral variable used here, so the public definition is reused.
   * Pinned Mathlib supplies `norm_sub_norm_le`, `HasDerivAt.div`, `norm_div`,
     and `norm_pow`, but no packaged sticky-tail transport estimate. Searches
     of the installed non-Mathlib Lake packages returned no related theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Weil.Budget.CaratheodoryScaleCovariance

namespace D5.S3.Weil.TestFunctions.StickyTailCompletionError

private theorem sticky_tail_kernel_estimates
    (r : Real) (z : Complex) (hz : ‖z‖ ≤ r) (hr : r < 1) :
    ∀ zeta : Complex, ‖zeta‖ = 1 →
      1 - r ≤ ‖zeta - z‖ ∧
      ‖zeta + z‖ ≤ 1 + r ∧
      ‖caratheodoryKernel zeta z‖ ≤ (1 + r) / (1 - r) ∧
      ‖caratheodoryKernel zeta z - 1‖ ≤ 2 * r / (1 - r) ∧
      HasDerivAt (fun eta : Complex => caratheodoryKernel eta z)
        ((-2 : Complex) * z / (zeta - z) ^ 2) zeta ∧
      ‖(-2 : Complex) * z / (zeta - z) ^ 2‖ ≤ 2 * r / (1 - r) ^ 2 := by
  intro zeta hzeta
  have hrnonnegative : 0 ≤ r := (norm_nonneg z).trans hz
  have hmargin : 0 < 1 - r := sub_pos.mpr hr
  have hden : 1 - r ≤ ‖zeta - z‖ := by
    calc
      1 - r ≤ 1 - ‖z‖ := sub_le_sub_left hz 1
      _ = ‖zeta‖ - ‖z‖ := by rw [hzeta]
      _ ≤ ‖zeta - z‖ := norm_sub_norm_le zeta z
  have hnum : ‖zeta + z‖ ≤ 1 + r := by
    calc
      ‖zeta + z‖ ≤ ‖zeta‖ + ‖z‖ := norm_add_le zeta z
      _ = 1 + ‖z‖ := by rw [hzeta]
      _ ≤ 1 + r := by linarith
  have hdenpos : 0 < ‖zeta - z‖ := hmargin.trans_le hden
  have hdenne : zeta - z ≠ 0 := norm_pos_iff.mp hdenpos
  have hkernel :
      ‖caratheodoryKernel zeta z‖ ≤ (1 + r) / (1 - r) := by
    unfold caratheodoryKernel
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum hmargin hden
  have htwonum : ‖(2 : Complex) * z‖ ≤ 2 * r := by
    simpa only [norm_mul, Complex.norm_two] using
      mul_le_mul_of_nonneg_left hz (by norm_num : (0 : Real) ≤ 2)
  have hkernelSub :
      ‖caratheodoryKernel zeta z - 1‖ ≤ 2 * r / (1 - r) := by
    have hid : caratheodoryKernel zeta z - 1 =
        (2 : Complex) * z / (zeta - z) := by
      unfold caratheodoryKernel
      field_simp [hdenne]
      ring
    rw [hid, norm_div]
    exact div_le_div₀ (by positivity) htwonum hmargin hden
  have hderiv :
      HasDerivAt (fun eta : Complex => caratheodoryKernel eta z)
        ((-2 : Complex) * z / (zeta - z) ^ 2) zeta := by
    have hnumerator :
        HasDerivAt (fun eta : Complex => eta + z) 1 zeta := by
      exact (hasDerivAt_id' zeta).add_const z
    have hdenominator :
        HasDerivAt (fun eta : Complex => eta - z) 1 zeta := by
      exact (hasDerivAt_id' zeta).sub_const z
    have hquotient := hnumerator.div hdenominator hdenne
    simp only [Pi.add_apply, Pi.sub_apply, id_eq, add_zero, sub_zero, one_mul,
      mul_one] at hquotient
    change HasDerivAt (fun eta : Complex => (eta + z) / (eta - z))
      ((-2 : Complex) * z / (zeta - z) ^ 2) zeta
    exact hquotient.congr_deriv (by
      field_simp [hdenne]
      ring)
  have hdenSq : (1 - r) ^ 2 ≤ ‖zeta - z‖ ^ 2 :=
    (sq_le_sq₀ hmargin.le (norm_nonneg _)).2 hden
  have hminusTwoNum : ‖(-2 : Complex) * z‖ ≤ 2 * r := by
    simpa only [norm_mul, norm_neg, Complex.norm_two] using
      mul_le_mul_of_nonneg_left hz (by norm_num : (0 : Real) ≤ 2)
  have hderivNorm :
      ‖(-2 : Complex) * z / (zeta - z) ^ 2‖ ≤ 2 * r / (1 - r) ^ 2 := by
    rw [norm_div, norm_pow]
    exact div_le_div₀ (by positivity) hminusTwoNum (by positivity) hdenSq
  exact ⟨hden, hnum, hkernel, hkernelSub, hderiv, hderivNorm⟩

/-- A nonnegative sticky-tail budget inherits the uniform boundary-kernel
derivative bound whenever its transport and summation step is controlled by
every such uniform bound. -/
theorem sticky_tail_completion_error
    (r D : Real) (z : Complex) (Cxi CT : Complex → Complex)
    (hz : ‖z‖ ≤ r) (hr : r < 1) (hD : 0 ≤ D)
    (transportControl :
      0 ≤ D → ∀ K : Real,
        (∀ zeta : Complex, ‖zeta‖ = 1 →
          ‖(-2 : Complex) * z / (zeta - z) ^ 2‖ ≤ K) →
        ‖Cxi z - CT z‖ ≤ K * D) :
    ‖Cxi z - CT z‖ ≤ (2 * r / (1 - r) ^ 2) * D := by
  have estimates := sticky_tail_kernel_estimates r z hz hr
  exact transportControl hD (2 * r / (1 - r) ^ 2) fun zeta hzeta =>
    (estimates zeta hzeta).2.2.2.2.2

example :
    ‖(1 : Complex) - ((1 / 2 : Real) : Complex)‖ = (1 / 2 : Real) ∧
    1 - (1 / 2 : Real) ≤
      ‖(1 : Complex) - ((1 / 2 : Real) : Complex)‖ ∧
    ‖(-1 : Complex) + ((1 / 2 : Real) : Complex)‖ = (1 / 2 : Real) ∧
    ‖(-1 : Complex) + ((1 / 2 : Real) : Complex)‖ ≤ 1 + (1 / 2 : Real) ∧
    2 * (1 / 2 : Real) / (1 - 1 / 2) ^ 2 = 4 := by
  norm_num [Complex.norm_def, Complex.normSq_apply]

#print axioms sticky_tail_completion_error

end D5.S3.Weil.TestFunctions.StickyTailCompletionError
