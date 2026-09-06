/- GID: D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingSecondJet
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilArithmeticCouplingSecondJet
   mirror-E: none(waiver:analytic-remainder-for-concrete-Weil-symbol)
   anchors: []
   digest: A second exterior divided-difference jet gains a further N/|m| factor for the actual arithmetic Weil boundary symbol. -/

import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Second arithmetic coupling jet

The first arithmetic coupling jet keeps the constant term in

  1 / (m - n) = 1 / m + n / (m * (m - n)).

For the fixed finite interior band and a distant exterior mode, one more exact
step gives

  1 / (m - n) = 1 / m + n / m^2 + n^2 / (m^2 * (m - n)).

Applied to the concrete pole-Gamma-prime boundary symbol from
`WeilArithmeticCouplingJet`, this gains a second power of `N / |m|` in the
pointwise exterior remainder.  No asymptotic replacement of the arithmetic
symbol is made and no exterior upper cutoff occurs in the theorem.

For a later square-summed tail certificate the retained second jet exposes the
four finite moments

  sum v_n,  sum s_n v_n,  sum n v_n,  sum n s_n v_n.

The infinite square summation and its low-rank Gram majorant are analytic
consequences recorded in the RH theory volume; they are not silently folded
into this pointwise Lean theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingSecondJet

open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-- The second exterior arithmetic jet retains both the zeroth and first
interior-index moments of the actual divided-difference coefficient. -/
def couplingSecondJet (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) : ℂ :=
  ∑ n ∈ S,
    ((((arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
        (Real.pi * (m : ℝ)) +
      (arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) * (n : ℝ) /
        (Real.pi * (m : ℝ) ^ 2) : ℝ) : ℂ) * v n)

private theorem coefficient_second_remainder
    {x y sn sm B N : ℝ}
    (hN : 0 ≤ N) (hx : |x| ≤ N) (hy : N < |y|)
    (hsn : |sn| ≤ B) (hsm : |sm| ≤ B) :
    |(sn - sm) / (Real.pi * (y - x)) -
        ((sn - sm) / (Real.pi * y) +
          (sn - sm) * x / (Real.pi * y ^ 2))| ≤
      2 * B * N ^ 2 /
        (Real.pi * |y| ^ 2 * (|y| - N)) := by
  have hB : 0 ≤ B := (abs_nonneg sn).trans hsn
  have hy0 : 0 < |y| := lt_of_le_of_lt hN hy
  have hgap : 0 < |y| - N := sub_pos.mpr hy
  have htri := abs_add_le (y - x) x
  rw [sub_add_cancel] at htri
  have hrev : |y| - N ≤ |y - x| := by linarith
  have hdiff : 0 < |y - x| := lt_of_lt_of_le hgap hrev
  have hyn : y ≠ 0 := abs_pos.mp hy0
  have hdn : y - x ≠ 0 := abs_pos.mp hdiff
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hx2 : |x| ^ 2 ≤ N ^ 2 := by nlinarith
  have hs : |sn - sm| ≤ 2 * B :=
    (abs_sub sn sm).trans (by linarith)
  have hnum : |sn - sm| * |x| ^ 2 ≤ 2 * B * N ^ 2 := by
    exact mul_le_mul hs hx2 (sq_nonneg _) (by positivity)
  have hid :
      (sn - sm) / (Real.pi * (y - x)) -
          ((sn - sm) / (Real.pi * y) +
            (sn - sm) * x / (Real.pi * y ^ 2)) =
        (sn - sm) * x ^ 2 /
          (Real.pi * y ^ 2 * (y - x)) := by
    field_simp [Real.pi_ne_zero, hyn, hdn]
    <;> ring
  have hden :
      Real.pi * |y| ^ 2 * (|y| - N) ≤
        Real.pi * |y| ^ 2 * |y - x| :=
    mul_le_mul_of_nonneg_left hrev (by positivity)
  rw [hid, abs_div, abs_mul, abs_pow, abs_mul, abs_mul,
    abs_of_pos Real.pi_pos, abs_pow]
  calc
    _ ≤ (2 * B * N ^ 2) /
        (Real.pi * |y| ^ 2 * |y - x|) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-- The actual arithmetic divided-difference column admits a second-order
exterior jet. Relative to the first-jet error, the numerator gains one more
factor `N` while the denominator gains one more factor `|m|`. Thus on an
exterior tail `|m| > M > N`, square summation gains a factor of order
`(N/M)^2`. -/
theorem arithmetic_coupling_second_jet_error
    {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) {N : ℝ} (hN : 0 ≤ N)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ N)
    {m : ℤ} (hm : N < |(m : ℝ)|) :
    ‖couplingColumn c S v m - couplingSecondJet c S v m‖ ≤
      (2 * arithmeticBoundaryBudget c * N ^ 2 /
        (Real.pi * |(m : ℝ)| ^ 2 * (|(m : ℝ)| - N))) *
          ∑ n ∈ S, ‖v n‖ := by
  let a (n : ℤ) : ℝ :=
    (arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
      (Real.pi * ((m : ℝ) - (n : ℝ)))
  let b (n : ℤ) : ℝ :=
    (arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
        (Real.pi * (m : ℝ)) +
      (arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) * (n : ℝ) /
        (Real.pi * (m : ℝ) ^ 2)
  let K : ℝ :=
    2 * arithmeticBoundaryBudget c * N ^ 2 /
      (Real.pi * |(m : ℝ)| ^ 2 * (|(m : ℝ)| - N))
  have hab (n : ℤ) (hn : n ∈ S) : |a n - b n| ≤ K :=
    coefficient_second_remainder hN (hS n hn) hm
      (arithmetic_boundary_symbol_bound hc n).2
      (arithmetic_boundary_symbol_bound hc m).2
  have heq :
      couplingColumn c S v m - couplingSecondJet c S v m =
        ∑ n ∈ S, ((a n - b n : ℝ) : ℂ) * v n := by
    unfold couplingColumn couplingSecondJet
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [a, b]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ∑ n ∈ S, ‖((a n - b n : ℝ) : ℂ) * v n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ S, K * ‖v n‖ :=
      Finset.sum_le_sum (fun n hn => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hab n hn) (norm_nonneg _))
    _ = _ := by
      rw [Finset.mul_sum]
      rfl

#print axioms arithmetic_coupling_second_jet_error

end D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingSecondJet
