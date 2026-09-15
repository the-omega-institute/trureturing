/- GID: D5/S3/Arith/Radical/GoldenRadicalDividedDifference
   generality: I
   mirror-B: D5/B/S3/Arith/Radical/GoldenRadicalDividedDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A divided geometric sum has an explicit quadratic integral certificate over the actual golden ring. -/

import D5.S0.Carrier.Ring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Radical.GoldenRadicalDividedDifference

open D5.S0.Carrier
open Finset Polynomial

/-- The homogeneous divided difference of `X^n`; no division occurs here. -/
def powerSum {R : Type*} [CommRing R] (n : ℕ) (x a : R) : R :=
  ∑ i ∈ range n, x ^ i * a ^ (n - 1 - i)

/-- The second divided difference, including its values at coincident inputs. -/
def secondDifference {R : Type*} [CommRing R] (n : ℕ) (x a : R) : R :=
  ∑ i ∈ range n, a ^ (n - 1 - i) * powerSum i x a

/-- The specified candidate integral element; the theorem requires `n > 0`. -/
def dividedPowerSum {L : Type*} [Field L] (n : ℕ) (x a : L) : L :=
  powerSum n x a / (n : L)

private lemma powerSum_mul_sub {R : Type*} [CommRing R]
    (n : ℕ) (x a : R) : powerSum n x a * (x - a) = x ^ n - a ^ n := by
  exact (Commute.all x a).geom_sum₂_mul n

private lemma powerSum_self {R : Type*} [CommRing R]
    (n : ℕ) (a : R) : powerSum n a a = (n : R) * a ^ (n - 1) := by
  exact geom_sum₂_self a n

private lemma secondDifference_mul_sub {R : Type*} [CommRing R]
    (n : ℕ) (x a : R) :
    secondDifference n x a * (x - a) =
      powerSum n x a - (n : R) * a ^ (n - 1) := by
  calc
    secondDifference n x a * (x - a) =
        ∑ i ∈ range n, a ^ (n - 1 - i) * (x ^ i - a ^ i) := by
      simp only [secondDifference, Finset.sum_mul, mul_assoc, powerSum_mul_sub]
    _ = powerSum n x a - powerSum n a a := by
      simp only [mul_sub, Finset.sum_sub_distrib, powerSum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ = powerSum n x a - (n : R) * a ^ (n - 1) := by
      rw [powerSum_self]

private lemma quadratic_certificate {L : Type*} [Field L] [CharZero L]
    (n : ℕ) (hn : 0 < n) (x a b : L)
    (hx : x ^ n = a ^ n + (n : L) ^ 2 * b) :
    let y := dividedPowerSum n x a
    (x - a) * y = (n : L) * b ∧
      y ^ 2 = a ^ (n - 1) * y + b * secondDifference n x a := by
  let y := dividedPowerSum n x a
  change (x - a) * y = (n : L) * b ∧
    y ^ 2 = a ^ (n - 1) * y + b * secondDifference n x a
  have hn0 : (n : L) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hny : (n : L) * y = powerSum n x a := by
    dsimp [y, dividedPowerSum]
    field_simp [hn0] <;> ring
  have hxy : (x - a) * y = (n : L) * b := by
    apply mul_left_cancel₀ hn0
    calc
      (n : L) * ((x - a) * y) = ((n : L) * y) * (x - a) := by ring
      _ = powerSum n x a * (x - a) := by rw [hny]
      _ = x ^ n - a ^ n := powerSum_mul_sub n x a
      _ = (n : L) * ((n : L) * b) := by rw [hx]; ring
  refine ⟨hxy, ?_⟩
  apply mul_left_cancel₀ hn0
  calc
    (n : L) * y ^ 2 = ((n : L) * y) * y := by ring
    _ = powerSum n x a * y := by rw [hny]
    _ = (secondDifference n x a * (x - a) +
          (n : L) * a ^ (n - 1)) * y := by
      rw [secondDifference_mul_sub]
      ring
    _ = secondDifference n x a * ((x - a) * y) +
          (n : L) * (a ^ (n - 1) * y) := by ring
    _ = (n : L) * (a ^ (n - 1) * y + b * secondDifference n x a) := by
      rw [hxy]
      ring

private lemma quadratic_integrality {L : Type*} [Field L]
    (y c₁ c₀ : L) (h₁ : IsIntegral ℤ c₁) (h₀ : IsIntegral ℤ c₀)
    (hy : y ^ 2 = c₁ * y + c₀) : IsIntegral ℤ y := by
  let P : L[X] := X ^ 2 - (C c₁ * X + C c₀)
  have hdeg : (C c₁ * X + C c₀ : L[X]).degree < (X ^ 2 : L[X]).degree := by
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_linear_lt
  have hmonic : P.Monic := (Polynomial.monic_X_pow 2).sub_of_left hdeg
  have hnat : P.natDegree = 2 := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    dsimp [P]
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hdeg, Polynomial.degree_X_pow]
  have hzero : P.eval y = 0 := by
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [hy, sub_self]
  apply IsIntegral.of_aeval_monic_of_isIntegral_coeff hmonic
      (by rw [hnat]; decide) (by rw [hzero]; exact isIntegral_zero)
  intro j
  by_cases hj₂ : j = 2
  · subst j
    simpa [P] using (isIntegral_one : IsIntegral ℤ (1 : L))
  by_cases hj₁ : j = 1
  · subst j
    simpa [P] using h₁.neg
  by_cases hj₀ : j = 0
  · subst j
    simpa [P] using h₀.neg
  simpa [P, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, hj₂, hj₁, hj₀, eq_comm] using
    (isIntegral_zero : IsIntegral ℤ (0 : L))

private lemma golden_integer_integral (z : GoldenInt) : IsIntegral ℤ z := by
  have hphi : IsIntegral ℤ phi := by
    let P : ℤ[X] := (X ^ 2 - C 1) - X
    have hP : P.Monic := by
      apply (Polynomial.monic_X_pow_sub_C (1 : ℤ) (by decide : 2 ≠ 0)).sub_of_left
      rw [Polynomial.degree_X,
        Polynomial.degree_X_pow_sub_C (by decide : 0 < 2)]
      norm_num
    refine ⟨P, hP, ?_⟩
    simp [P, phi_sq]
  have ha : IsIntegral ℤ (z.a : GoldenInt) := isIntegral_algebraMap
  have hb : IsIntegral ℤ (z.b : GoldenInt) := isIntegral_algebraMap
  have hz : z = (z.a : GoldenInt) + (z.b : GoldenInt) * phi := by
    ext <;> simp [phi]
  rw [hz]
  exact ha.add (hb.mul hphi)

/-- A positive radical degree and a genuine square-modulus lift in the fixed golden
ring yield an explicit algebraic integer. The quadratic equation is over integral
coefficients that may contain `theta`; no degree-two claim over `ℚ(√5)` is made.
The lift is a hypothesis, not a claim that a WSS prime has been constructed. -/
theorem result {L : Type*} [Field L] [CharZero L]
    (ι : GoldenInt →+* L) (n : ℕ) (hn : 0 < n)
    (a b : GoldenInt) (theta : L)
    (hroot : theta ^ n = ι phi)
    (hlift : phi = a ^ n + (n : GoldenInt) ^ 2 * b) :
    let y := dividedPowerSum n theta (ι a)
    (theta - ι a) * y = (n : L) * ι b ∧
      y ^ 2 = (ι a) ^ (n - 1) * y + ι b * secondDifference n theta (ι a) ∧
      IsIntegral ℤ y := by
  let y := dividedPowerSum n theta (ι a)
  change (theta - ι a) * y = (n : L) * ι b ∧
    y ^ 2 = (ι a) ^ (n - 1) * y + ι b * secondDifference n theta (ι a) ∧
    IsIntegral ℤ y
  have hpow : theta ^ n = (ι a) ^ n + (n : L) ^ 2 * ι b := by
    rw [hroot, hlift]
    simp only [map_add, map_mul, map_pow, map_natCast]
  have hcert := quadratic_certificate n hn theta (ι a) (ι b) hpow
  change (theta - ι a) * y = (n : L) * ι b ∧
    y ^ 2 = (ι a) ^ (n - 1) * y + ι b * secondDifference n theta (ι a) at hcert
  refine ⟨hcert.1, hcert.2, ?_⟩
  have ha : IsIntegral ℤ (ι a) := map_isIntegral_int ι (golden_integer_integral a)
  have hb : IsIntegral ℤ (ι b) := map_isIntegral_int ι (golden_integer_integral b)
  have htheta : IsIntegral ℤ theta := by
    apply IsIntegral.of_pow hn
    rw [hroot]
    exact map_isIntegral_int ι (golden_integer_integral phi)
  have hsecond : IsIntegral ℤ (secondDifference n theta (ι a)) := by
    unfold secondDifference
    apply IsIntegral.sum
    intro i hi
    apply (ha.pow (n - 1 - i)).mul
    unfold powerSum
    apply IsIntegral.sum
    intro j hj
    exact (htheta.pow j).mul (ha.pow (i - 1 - j))
  exact quadratic_integrality y ((ι a) ^ (n - 1))
    (ι b * secondDifference n theta (ι a))
    (ha.pow (n - 1)) (hb.mul hsecond) hcert.2

#print axioms result

end D5.S3.Arith.Radical.GoldenRadicalDividedDifference
