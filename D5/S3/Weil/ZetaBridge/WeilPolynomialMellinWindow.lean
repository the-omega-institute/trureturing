/- GID: D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow
   mirror-E: none(waiver:separate-certified-prolate-spectral-realization)
   anchors: []
   digest: The actual paper Fourier transform of a finite polynomial arithmetic Mellin window is an explicit finite endpoint sum, with integrability proved. -/

import D5.S3.Weil.ZetaCore.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Polynomial realizations of the prolate arithmetic window

For a polynomial h(t)=sum_r A_r*t^(2*r), the summand belonging to integer m
is exp(x/2)*h(m*exp(x)) on (-a,a-log(m)]. The union of these explicitly
specified intervals implements the finite arithmetic Mellin sum with zero
extension. Endpoints do not change the Lebesgue Fourier transform.

The owner is `Zeta23.paperFT`, not a parallel Fourier or Xi definition.
The main theorem evaluates the actual integral without a quadrature hypothesis.
It applies on Im(z)<1/2, where all endpoint denominators are proved nonzero.
Its concrete consumer is the interval-certified Legendre polynomial of the
zero-integral span of the zeroth and fourth prolate modes. Spectral isolation
of those modes and the infinite Legendre tail are separate paper/computer-
assisted steps, not assumptions disguised as the conclusions below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilPolynomialMellinWindow

open MeasureTheory Set
open scoped BigOperators

/-- The exponent after the actual Fourier kernel is inserted. -/
def mellinRate (r : ℕ) (z : ℂ) : ℂ :=
  ((2 * r : ℕ) : ℂ) + 1 / 2 + Complex.I * z

/-- The m-th arithmetic summand for the monomial t^(2*r), zero extended. -/
def mellinMonomial (a : ℝ) (m r : ℕ) (x : ℝ) : ℂ :=
  (Ioc (-a) (a - Real.log (m : ℝ))).indicator
    (fun x : ℝ => (m : ℂ) ^ (2 * r) *
      Complex.exp ((((2 * r : ℕ) : ℂ) + 1 / 2) * (x : ℂ))) x

/-- A finite polynomial arithmetic Mellin window, including its scalar 4. -/
def polynomialMellinWindow (a : ℝ) (M d : ℕ) (A : ℕ → ℂ) (x : ℝ) : ℂ :=
  4 * ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.range d,
    A r * mellinMonomial a m r x

/-- The exponential coordinates are exactly the polynomial arithmetic
summand, including the half-power Jacobian. -/
theorem mellin_monomial_polynomial_value (a x : ℝ) (m r : ℕ) :
    mellinMonomial a m r x =
      (Ioc (-a) (a - Real.log (m : ℝ))).indicator
        (fun x : ℝ => Complex.exp ((x : ℂ) / 2) *
          ((m : ℂ) * Complex.exp (x : ℂ)) ^ (2 * r)) x := by
  classical
  by_cases hx : x ∈ Ioc (-a) (a - Real.log (m : ℝ))
  · simp only [mellinMonomial, indicator_of_mem hx]
    rw [mul_pow, ← Complex.exp_nat_mul (x : ℂ) (2 * r)]
    have hid : (((2 * r : ℕ) : ℂ) + 1 / 2) * (x : ℂ) =
        ((2 * r : ℕ) : ℂ) * (x : ℂ) + (x : ℂ) / 2 := by ring
    rw [hid, Complex.exp_add]
    ring
  · simp only [mellinMonomial, indicator_of_not_mem hx]

private theorem kernel_identity (a x : ℝ) (m r : ℕ) (z : ℂ) :
    mellinMonomial a m r x * Complex.exp (Complex.I * z * (x : ℂ)) =
      (Ioc (-a) (a - Real.log (m : ℝ))).indicator
        (fun x : ℝ => (m : ℂ) ^ (2 * r) *
          Complex.exp (mellinRate r z * (x : ℂ))) x := by
  classical
  by_cases hx : x ∈ Ioc (-a) (a - Real.log (m : ℝ))
  · simp only [mellinMonomial, indicator_of_mem hx]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [mellinRate]
    ring
  · simp [mellinMonomial, hx]

private theorem monomial_kernel_integrable (a : ℝ) (m r : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ => mellinMonomial a m r x *
      Complex.exp (Complex.I * z * (x : ℂ))) := by
  simp_rw [kernel_identity]
  have h : Continuous (fun x : ℝ => (m : ℂ) ^ (2 * r) *
      Complex.exp (mellinRate r z * (x : ℂ))) := by fun_prop
  exact (h.intervalIntegrable (-a) (a - Real.log (m : ℝ))).1.indicator measurableSet_Ioc

private theorem finite_sum_integrable {ι : Type*} (S : Finset ι)
    (F : ι → ℝ → ℂ) (hF : ∀ i ∈ S, Integrable (F i)) :
    Integrable (fun x => ∑ i ∈ S, F i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (integrable_zero : Integrable (fun _ : ℝ => (0 : ℂ)))
  | @insert i S hi ih =>
      have hs : ∀ j ∈ S, Integrable (F j) :=
        fun j hj => hF j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi] using
        (hF i (Finset.mem_insert_self i S)).add (ih hs)

private theorem integral_finite_sum {ι : Type*} (S : Finset ι)
    (F : ι → ℝ → ℂ) (hF : ∀ i ∈ S, Integrable (F i)) :
    (∫ x : ℝ, ∑ i ∈ S, F i x) = ∑ i ∈ S, ∫ x : ℝ, F i x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hs : ∀ j ∈ S, Integrable (F j) :=
        fun j hj => hF j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      rw [integral_add (hF i (Finset.mem_insert_self i S))
        (finite_sum_integrable S F hs), ih hs]

private theorem rate_ne_zero (r : ℕ) {z : ℂ} (hz : z.im < 1 / 2) :
    mellinRate r z ≠ 0 := by
  have hr : 0 ≤ ((2 * r : ℕ) : ℝ) := Nat.cast_nonneg _
  have he : (mellinRate r z).re = ((2 * r : ℕ) : ℝ) + 1 / 2 - z.im := by
    norm_num [mellinRate, Complex.mul_re]
  intro h
  have hh := congrArg Complex.re h
  rw [he, Complex.zero_re] at hh
  linarith

private theorem monomial_paperFT (a : ℝ) (m r : ℕ) (z : ℂ)
    (hcut : Real.log (m : ℝ) ≤ 2 * a) (hz : z.im < 1 / 2) :
    Zeta23.paperFT (mellinMonomial a m r) z =
      (m : ℂ) ^ (2 * r) *
        ((Complex.exp (mellinRate r z * ((a - Real.log (m : ℝ) : ℝ) : ℂ)) -
          Complex.exp (mellinRate r z * ((-a : ℝ) : ℂ))) / mellinRate r z) := by
  unfold Zeta23.paperFT
  simp_rw [kernel_identity]
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (show -a ≤ a - Real.log (m : ℝ) by linarith),
    intervalIntegral.integral_const_mul, integral_exp_mul_complex (rate_ne_zero r hz)]

/-- Every complex Fourier integrand of the finite arithmetic window is
integrable. This is proved even outside the strip used for the endpoint formula. -/
theorem polynomial_mellin_fourier_integrable
    (a : ℝ) (M d : ℕ) (A : ℕ → ℂ) (z : ℂ) :
    Integrable (fun x : ℝ => polynomialMellinWindow a M d A x *
      Complex.exp (Complex.I * z * (x : ℂ))) := by
  have h (m r : ℕ) : Integrable (fun x : ℝ =>
      A r * (mellinMonomial a m r x * Complex.exp (Complex.I * z * (x : ℂ)))) :=
    (monomial_kernel_integrable a m r z).const_mul (A r)
  have hs := finite_sum_integrable (Finset.Icc 1 M)
    (fun m x => ∑ r ∈ Finset.range d,
      A r * (mellinMonomial a m r x * Complex.exp (Complex.I * z * (x : ℂ))))
    (fun m _ => finite_sum_integrable (Finset.range d) _ (fun r _ => h m r))
  simpa only [polynomialMellinWindow, Finset.sum_mul, mul_assoc] using hs.const_mul (4 : ℂ)

/-- Exact finite endpoint evaluation of the repository's actual `paperFT`.
The support cutoff covers precisely the arithmetic summands with log(m)<=2a.
No candidate transform, zero data, quadrature accuracy, integrability or spectral
hypothesis is supplied as an input. -/
theorem polynomial_mellin_window_paperFT
    (a : ℝ) (M d : ℕ) (A : ℕ → ℂ) (z : ℂ)
    (hcut : ∀ m ∈ Finset.Icc 1 M, Real.log (m : ℝ) ≤ 2 * a)
    (hz : z.im < 1 / 2) :
    Zeta23.paperFT (polynomialMellinWindow a M d A) z =
      4 * ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.range d,
        A r * ((m : ℂ) ^ (2 * r) *
          ((Complex.exp (mellinRate r z * ((a - Real.log (m : ℝ) : ℝ) : ℂ)) -
            Complex.exp (mellinRate r z * ((-a : ℝ) : ℂ))) / mellinRate r z)) := by
  let F (m r : ℕ) (x : ℝ) : ℂ :=
    A r * (mellinMonomial a m r x * Complex.exp (Complex.I * z * (x : ℂ)))
  have hF (m r : ℕ) : Integrable (F m r) :=
    (monomial_kernel_integrable a m r z).const_mul (A r)
  have hid : (fun x : ℝ => polynomialMellinWindow a M d A x *
      Complex.exp (Complex.I * z * (x : ℂ))) =
      (fun x : ℝ => 4 * ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.range d, F m r x) := by
    funext x
    simp only [polynomialMellinWindow, Finset.sum_mul, mul_assoc, F]
  unfold Zeta23.paperFT
  rw [hid, integral_const_mul,
    integral_finite_sum (Finset.Icc 1 M) _
      (fun m _ => finite_sum_integrable (Finset.range d) _ (fun r _ => hF m r))]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finite_sum (Finset.range d) _ (fun r _ => hF m r)]
  apply Finset.sum_congr rfl
  intro r hr
  change (∫ x : ℝ, A r *
      (mellinMonomial a m r x * Complex.exp (Complex.I * z * (x : ℂ)))) = _
  rw [integral_const_mul]
  exact congrArg (fun w : ℂ => A r * w) (monomial_paperFT a m r z (hcut m hm) hz)

#print axioms mellin_monomial_polynomial_value
#print axioms polynomial_mellin_fourier_integrable
#print axioms polynomial_mellin_window_paperFT

end D5.S3.Weil.ZetaBridge.WeilPolynomialMellinWindow
