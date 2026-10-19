/- GID: D5/S3/Weil/ZetaBridge/PrimePolynomialInterference
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PrimePolynomialInterference
   mirror-E: none(waiver:analytic-prime-polynomial-interference-without-executable-mirror)
   anchors: []
   utility: none
   digest: Actual finite-prime polynomial interference on a dyadic block is bounded uniformly in its length by coefficient energies. -/

import D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.PrimePolynomialInterference

open scoped BigOperators
open Polynomial

private theorem increasing_abel_bound (x w : ℕ → ℝ) (H : ℝ) (n : ℕ)
    (hH : 0 ≤ H) (hw : ∀ j, 0 ≤ w j) (hmono : Monotone w)
    (hprefix : ∀ l, |∑ j ∈ Finset.range l, x j| ≤ H) :
    |∑ j ∈ Finset.range n, x j * w j| ≤ 2 * H * w (n - 1) := by
  have hparts := Finset.sum_range_by_parts' x w n
  simp only [smul_eq_mul] at hparts
  have hdiff (j : ℕ) : 0 ≤ w (j + 1) - w j :=
    sub_nonneg.mpr (hmono (Nat.le_succ j))
  have htel (l : ℕ) :
      (∑ j ∈ Finset.range l, (w (j + 1) - w j)) = w l - w 0 := by
    induction l with
    | zero => simp
    | succ l ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hfirst : |(∑ j ∈ Finset.range n, x j) * w (n - 1)| ≤
      H * w (n - 1) := by
    rw [abs_mul, abs_of_nonneg (hw (n - 1))]
    exact mul_le_mul_of_nonneg_right (hprefix n) (hw (n - 1))
  have hrest :
      |∑ j ∈ Finset.range (n - 1),
        (∑ i ∈ Finset.range (j + 1), x i) * (w (j + 1) - w j)| ≤
        H * (w (n - 1) - w 0) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n - 1),
          |(∑ i ∈ Finset.range (j + 1), x i) * (w (j + 1) - w j)| := by
        simpa only [Real.norm_eq_abs] using
          (norm_sum_le (Finset.range (n - 1))
            (fun j => (∑ i ∈ Finset.range (j + 1), x i) * (w (j + 1) - w j)))
      _ ≤ ∑ j ∈ Finset.range (n - 1), H * (w (j + 1) - w j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (hdiff j)]
        exact mul_le_mul_of_nonneg_right (hprefix (j + 1)) (hdiff j)
      _ = H * (w (n - 1) - w 0) := by
        rw [← Finset.mul_sum, htel]
  rw [hparts]
  calc
    _ ≤ |(∑ j ∈ Finset.range n, x j) * w (n - 1)| +
        |∑ j ∈ Finset.range (n - 1),
          (∑ i ∈ Finset.range (j + 1), x i) * (w (j + 1) - w j)| := abs_sub _ _
    _ ≤ H * w (n - 1) + H * (w (n - 1) - w 0) := add_le_add hfirst hrest
    _ ≤ 2 * H * w (n - 1) := by
      nlinarith only [mul_nonneg hH (hw 0)]

private theorem prime_monomial_bound {c : ℕ} (hc : 2 ≤ c)
    {N : ℕ} (hN : 0 < N) (hH : 0 ≤ ActualFullSymbolTail.primeFirstMoment c)
    (k : ℕ) :
    |∑ j ∈ Finset.range N,
      PrimeSymbolMeanSquare.primeSymbol c ((N + j + 1 : ℕ) : ℤ) *
        (((N + j + 1 : ℕ) : ℝ) / (N : ℝ)) ^ k| ≤
      2 * ActualFullSymbolTail.primeFirstMoment c * (2 : ℝ) ^ k := by
  let x : ℕ → ℝ := fun j =>
    PrimeSymbolMeanSquare.primeSymbol c ((N + j + 1 : ℕ) : ℤ)
  let t : ℕ → ℝ := fun j => ((N + j + 1 : ℕ) : ℝ) / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ht (j : ℕ) : 0 ≤ t j :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hNR)
  have htmono : Monotone t := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ (le_of_lt hNR)
    exact_mod_cast (show N + i + 1 ≤ N + j + 1 by omega)
  have hwmono : Monotone (fun j => t j ^ k) := by
    intro i j hij
    induction k with
    | zero => simp
    | succ k ih =>
        change t i ^ (k + 1) ≤ t j ^ (k + 1)
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih (htmono hij) (ht i) (pow_nonneg (ht j) k)
  have hprefix (l : ℕ) :
      |∑ j ∈ Finset.range l, x j| ≤ ActualFullSymbolTail.primeFirstMoment c := by
    have he (j : ℕ) : (N : ℤ) + 1 + (j : ℤ) = ((N + j + 1 : ℕ) : ℤ) := by
      push_cast <;> ring
    simpa only [x, he] using
      ActualFullSymbolTail.prime_first_moment_block hc ((N : ℤ) + 1) l
  have hend : t (N - 1) = 2 := by
    dsimp only [t]
    have he : N + (N - 1) + 1 = 2 * N := by omega
    rw [he]
    apply (div_eq_iff (ne_of_gt hNR)).2
    push_cast <;> ring
  change |∑ j ∈ Finset.range N, x j * t j ^ k| ≤ _
  calc
    _ ≤ 2 * ActualFullSymbolTail.primeFirstMoment c * t (N - 1) ^ k :=
      increasing_abel_bound x (fun j => t j ^ k)
        (ActualFullSymbolTail.primeFirstMoment c) N hH
        (fun j => pow_nonneg (ht j) k) hwmono hprefix
    _ = _ := by rw [hend]

private theorem eval_cross (d : ℕ) (F B : ℂ[X])
    (hF : F.natDegree < d) (hB : B.natDegree < d) (t : ℝ) :
    (F.eval (t : ℂ) * star (B.eval (t : ℂ))).re =
      ∑ r ∈ Finset.range d, ∑ s ∈ Finset.range d,
        (F.coeff r * star (B.coeff s)).re * t ^ (r + s) := by
  have htstar : star (t : ℂ) = (t : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
  have hexp : F.eval (t : ℂ) * star (B.eval (t : ℂ)) =
      ∑ r ∈ Finset.range d, ∑ s ∈ Finset.range d,
        (F.coeff r * star (B.coeff s)) * ((t ^ (r + s) : ℝ) : ℂ) := by
    rw [Polynomial.eval_eq_sum_range' hF, Polynomial.eval_eq_sum_range' hB]
    simp only [star_sum, star_mul, star_pow, htstar]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [Complex.ofReal_pow, pow_add]
    ring
  rw [hexp]
  change Complex.reAddGroupHom _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  change Complex.reAddGroupHom _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  change (F.coeff r * star (B.coeff s) * ((t ^ (r + s) : ℝ) : ℂ)).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem coefficient_cauchy (d : ℕ) (F : ℂ[X]) :
    (∑ r ∈ Finset.range d, ‖F.coeff r‖ * (2 : ℝ) ^ r) ^ 2 ≤
      (∑ r ∈ Finset.range d, (4 : ℝ) ^ r) *
        (∑ r ∈ Finset.range d, ‖F.coeff r‖ ^ 2) := by
  have hpow (r : ℕ) : ((2 : ℝ) ^ r) ^ 2 = (4 : ℝ) ^ r := by
    rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
    norm_num
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range d)
    (fun r => ‖F.coeff r‖) (fun r => (2 : ℝ) ^ r)
  simpa only [hpow, mul_comm] using hcs

private theorem polynomial_sum_bound (s : Finset ℕ) (x t : ℕ → ℝ)
    (H : ℝ) (hH : 0 ≤ H)
    (hmoment : ∀ k : ℕ, |∑ j ∈ s, x j * t j ^ k| ≤ 2 * H * (2 : ℝ) ^ k)
    (d : ℕ) (F B : ℂ[X]) (hF : F.natDegree < d) (hB : B.natDegree < d) :
    |∑ j ∈ s, x j * (F.eval (t j : ℂ) * star (B.eval (t j : ℂ))).re| ≤
      H * (∑ r ∈ Finset.range d, (4 : ℝ) ^ r) *
        ((∑ r ∈ Finset.range d, ‖F.coeff r‖ ^ 2) +
          ∑ r ∈ Finset.range d, ‖B.coeff r‖ ^ 2) := by
  classical
  let LF : ℝ := ∑ r ∈ Finset.range d, ‖F.coeff r‖ * (2 : ℝ) ^ r
  let LB : ℝ := ∑ r ∈ Finset.range d, ‖B.coeff r‖ * (2 : ℝ) ^ r
  have hexp :
      (∑ j ∈ s, x j * (F.eval (t j : ℂ) * star (B.eval (t j : ℂ))).re) =
        ∑ r ∈ Finset.range d, ∑ q ∈ Finset.range d,
          (F.coeff r * star (B.coeff q)).re * (∑ j ∈ s, x j * t j ^ (r + q)) := by
    conv_lhs => simp only [eval_cross d F B hF hB, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcoeff (r q : ℕ) :
      |(F.coeff r * star (B.coeff q)).re| ≤ ‖F.coeff r‖ * ‖B.coeff q‖ := by
    simpa only [norm_mul, norm_star] using
      Complex.abs_re_le_norm (F.coeff r * star (B.coeff q))
  have hcross :
      |∑ j ∈ s, x j * (F.eval (t j : ℂ) * star (B.eval (t j : ℂ))).re| ≤
        2 * H * LF * LB := by
    rw [hexp]
    calc
      _ ≤ ∑ r ∈ Finset.range d,
          |∑ q ∈ Finset.range d,
            (F.coeff r * star (B.coeff q)).re * (∑ j ∈ s, x j * t j ^ (r + q))| := by
        simpa only [Real.norm_eq_abs] using (norm_sum_le (Finset.range d)
          (fun r => ∑ q ∈ Finset.range d,
            (F.coeff r * star (B.coeff q)).re * (∑ j ∈ s, x j * t j ^ (r + q))))
      _ ≤ ∑ r ∈ Finset.range d, ∑ q ∈ Finset.range d,
          |(F.coeff r * star (B.coeff q)).re * (∑ j ∈ s, x j * t j ^ (r + q))| := by
        apply Finset.sum_le_sum
        intro r _
        simpa only [Real.norm_eq_abs] using (norm_sum_le (Finset.range d)
          (fun q => (F.coeff r * star (B.coeff q)).re *
            (∑ j ∈ s, x j * t j ^ (r + q))))
      _ ≤ ∑ r ∈ Finset.range d, ∑ q ∈ Finset.range d,
          ‖F.coeff r‖ * ‖B.coeff q‖ * (2 * H * (2 : ℝ) ^ (r + q)) := by
        apply Finset.sum_le_sum
        intro r _
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul]
        exact mul_le_mul (hcoeff r q) (hmoment (r + q)) (abs_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ∑ r ∈ Finset.range d, (2 * H) * (‖F.coeff r‖ * (2 : ℝ) ^ r) * LB := by
        apply Finset.sum_congr rfl
        intro r _
        dsimp only [LB]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [pow_add]
        ring
      _ = 2 * H * LF * LB := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hyoung : 2 * LF * LB ≤
      (∑ r ∈ Finset.range d, (4 : ℝ) ^ r) *
        ((∑ r ∈ Finset.range d, ‖F.coeff r‖ ^ 2) +
          ∑ r ∈ Finset.range d, ‖B.coeff r‖ ^ 2) := by
    have hFc := coefficient_cauchy d F
    have hBc := coefficient_cauchy d B
    change LF ^ 2 ≤ _ at hFc
    change LB ^ 2 ≤ _ at hBc
    nlinarith only [sq_nonneg (LF - LB), hFc, hBc]
  calc
    _ ≤ 2 * H * LF * LB := hcross
    _ = H * (2 * LF * LB) := by ring
    _ ≤ H * ((∑ r ∈ Finset.range d, (4 : ℝ) ^ r) *
        ((∑ r ∈ Finset.range d, ‖F.coeff r‖ ^ 2) +
          ∑ r ∈ Finset.range d, ‖B.coeff r‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hyoung hH
    _ = _ := by ring

/-- Signed interference of two bounded-degree polynomials with the actual finite
prime symbol is controlled by their coefficient energies, independently of N. -/
theorem prime_polynomial_interference_bound {c : ℕ} (hc : 2 ≤ c)
    (d : ℕ) {N : ℕ} (hN : 0 < N) (F B : ℂ[X])
    (hF : F.natDegree < d) (hB : B.natDegree < d) :
    |∑ m ∈ Finset.Icc (N + 1) (2 * N),
      PrimeSymbolMeanSquare.primeSymbol c (m : ℤ) *
        (F.eval ((m : ℂ) / (N : ℂ)) *
          star (B.eval ((m : ℂ) / (N : ℂ)))).re| ≤
      ActualFullSymbolTail.primeFirstMoment c *
        (∑ r ∈ Finset.range d, (4 : ℝ) ^ r) *
        ((∑ r ∈ Finset.range d, ‖F.coeff r‖ ^ 2) +
          ∑ r ∈ Finset.range d, ‖B.coeff r‖ ^ 2) := by
  classical
  have hH : 0 ≤ ActualFullSymbolTail.primeFirstMoment c := by
    unfold ActualFullSymbolTail.primeFirstMoment
    apply Finset.sum_nonneg
    intro q _
    exact div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (norm_nonneg _)
  have hindex (f : ℕ → ℝ) :
      (∑ m ∈ Finset.Icc (N + 1) (2 * N), f m) =
        ∑ j ∈ Finset.range N, f (N + j + 1) := by
    calc
      _ = ∑ m ∈ Finset.Ico (N + 1) (2 * N + 1), f m := by
        rw [Finset.Ico_add_one_right_eq_Icc]
      _ = ∑ j ∈ Finset.range ((2 * N + 1) - (N + 1)), f ((N + 1) + j) :=
        Finset.sum_Ico_eq_sum_range f (N + 1) (2 * N + 1)
      _ = ∑ j ∈ Finset.range N, f (N + j + 1) := by
        have hlen : (2 * N + 1) - (N + 1) = N := by omega
        rw [hlen]
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        omega
  rw [hindex]
  have hcast (j : ℕ) :
      (((((N + j + 1 : ℕ) : ℝ) / (N : ℝ)) : ℝ) : ℂ) =
        ((N + j + 1 : ℕ) : ℂ) / (N : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_natCast]
  have h := polynomial_sum_bound (Finset.range N)
    (fun j => PrimeSymbolMeanSquare.primeSymbol c ((N + j + 1 : ℕ) : ℤ))
    (fun j => ((N + j + 1 : ℕ) : ℝ) / (N : ℝ))
    (ActualFullSymbolTail.primeFirstMoment c) hH
    (fun k => prime_monomial_bound hc hN hH k) d F B hF hB
  simpa only [hcast] using h

end D5.S3.Weil.ZetaBridge.PrimePolynomialInterference
