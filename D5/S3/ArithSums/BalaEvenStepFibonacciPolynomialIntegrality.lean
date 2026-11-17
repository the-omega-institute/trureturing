/- GID: D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality
   generality: I
   mirror-B: D5/B/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive even Fibonacci-polynomial steps have integral odd product-sum quotients. -/

/-
admission_basis: open-problem-resolution (#22966; Proved)
No escape witness is claimed for admission.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27594
Direct frozen dependencies use declaration identities from the protected base.
The doubling entry retains its original private identity; its public identity requires the canonical scope report.
F1: D5/S0/Observation/MatrixTracePowerSum.pow_add_two; sha256:477f52a1cada3768c6c6695f7bf1e92216cc53ac6f22ad3f67270f1f31f452be.
F2: D5/S1/Recurrence/LucasCompanion.companion_power_det; sha256:e1b30b86e76f3c1e12ca500be9a741df23d5d375f4c09e9d4a33f98c0dc6e7be.
F3: D5/S1/Recurrence/LucasEvenDescent.companion; sha256:4d31dffe5326b90f2855cb5c386b4cbe94ecff2fd9b817b5ebab0e1729b0c59b.
F4: D5/S1/Recurrence/LucasEvenDescent.doubling; sha256:967560dfa59b2ae139ece1266644d996710adb43662ff40a97f6bdf151d2880d (original private identity).
F5: D5/S1/Recurrence/LucasEvenDescent.lucasU; sha256:cbeb592ae9fb671d629aef82ed1fd47ca5fa1f30e75e1da7b0a4089da4600755.
F6: D5/S1/Recurrence/LucasEvenDescent.lucasU._proof_1; sha256:4607e6efd1e531e52d1e8fd0afe31731b21ad0f90a13523dac49f4c0e60d899c.
F7: D5/S1/Recurrence/LucasEvenDescent.lucas_recurrence; sha256:39d6470d149e167128d5ec12105960a15c1dc3c275b305837aad38e50b0c230e.
F8: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients.fibonacciRecurrencePolynomial; sha256:dec3bc2ef7e1abe50a03bced4302273e87228f3938799660320d46cc992100c8.
F9: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients.fibonacciRecurrencePolynomial.eq_1; sha256:5152fd7bb5f9da4de634f4d31a03ac17e0fde129abf3467ef11bea89caf3bc60.
F10: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients.fibonacci_recurrence_polynomial_coefficients; sha256:dc61222406063eade41b73f0e97dac9b0cdc6aad596614441fcee71c68767796.
F11: D5/S1/Recurrence/LucasEvenDescent.powerMatrix; sha256:7c3919366b4d98078349009599f0e05f4dcaee3ba1bf2f275bd0bc76bc562a56 (private compiled constant: _private.D5.S1.Recurrence.LucasEvenDescent.0.D5.S1.Recurrence.LucasEvenDescent.powerMatrix).
F12: D5/S1/Recurrence/LucasEvenDescent.power_add; sha256:2d2b705e1dc2b5f3b9a2ee1bd95356ed0e02a2d2dc271e587b2eca749e7b9736 (private compiled constant: _private.D5.S1.Recurrence.LucasEvenDescent.0.D5.S1.Recurrence.LucasEvenDescent.power_add).
F13: D5/S1/Recurrence/LucasEvenDescent.power_shape; sha256:e8f97983a6fc440a8f0ccb6376fb6d77aacb0c9274acadf1094f83c6ac6af821 (private compiled constant: _private.D5.S1.Recurrence.LucasEvenDescent.0.D5.S1.Recurrence.LucasEvenDescent.power_shape).
numerator: proof_shape: bind-only; escape_witness: none; consumers: claim, polynomial_quotient, result; Direct frozen dependencies: F8.
denominator: proof_shape: bind-only; escape_witness: none; consumers: claim, denominator_top_coeff, polynomial_quotient, result; Direct frozen dependencies: F8.
claim: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: F8.
u_zero: proof_shape: bind-only; escape_witness: none; consumers: even_step_reduction, u_sum; Direct frozen dependencies: F5, F7.
u_one: proof_shape: bind-only; escape_witness: none; consumers: even_step_reduction, scaled_product_quotient, u_sum; Direct frozen dependencies: F5, F7.
u_rec: proof_shape: bind-only; escape_witness: none; consumers: even_step_reduction, u_sum; Direct frozen dependencies: F5, F7.
u_doubling: proof_shape: bind-only; escape_witness: none; consumers: scaled_product_quotient, u_sum; Direct frozen dependencies: F4, F5.
u_sum: proof_shape: content; escape_witness: u_sum; consumers: scaled_product_quotient; Direct frozen dependencies: F4, F5, F7.
f_eq_lucas: proof_shape: bind-only; escape_witness: none; consumers: even_step_reduction; Direct frozen dependencies: F5, F7, F8.
even_step_reduction: proof_shape: bind-only; escape_witness: none; consumers: polynomial_quotient; Direct frozen dependencies: F1, F2, F3, F5, F6, F7, F8, F9.
denominator_top_coeff: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: F8, F10.
scaled_product_quotient: proof_shape: content; escape_witness: u_sum; consumers: polynomial_quotient; Direct frozen dependencies: F4, F5, F7.
polynomial_quotient: proof_shape: content; escape_witness: u_sum; consumers: result; Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9.
result: proof_shape: content; escape_witness: u_sum; consumers: none (settling result); Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10.
The odd partial-sum induction is the non-binding step in the four content classifications.
The quotient is an equality in rational functions, with no pointwise division assertion at a root.
Bibliographic completeness is ASSUMED-UNVERIFIED.
-/

import D5.S1.Recurrence.LucasEvenDescent
import D5.S1.Recurrence.LucasCompanion
import D5.S0.Observation.MatrixTracePowerSum
import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients

/-!
The even-step companion power has determinant one. Its Lucas recurrence gives a
factorization of each odd partial sum and an explicit integral product quotient.
-/

namespace D5.S3.ArithSums.BalaEvenStepFibonacciPolynomialIntegrality

open Polynomial
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
open D5.S1.Recurrence.LucasEvenDescent

/-- Product over the source's inclusive range 1 through 2n+1. -/
noncomputable def numerator (m n : ℕ) : ℤ[X] :=
  ∏ k ∈ Finset.Icc 1 (2 * n + 1), fibonacciRecurrencePolynomial (m * k)

/-- Sum over the same inclusive range. -/
noncomputable def denominator (m n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.Icc 1 (2 * n + 1), fibonacciRecurrencePolynomial (m * k)

/-- Bala's second COMMENT in OEIS A349272, with the preceding COMMENT's
positive-even-step restriction and the entry's zero-based offset. -/
def claim : Prop :=
  ∀ (m : ℕ) (n : ℕ), 2 ≤ m → Even m →
    denominator m n ≠ 0 ∧
      ∃ H : ℤ[X],
        algebraMap ℚ[X] (RatFunc ℚ) ((numerator m n).map (Int.castRingHom ℚ)) /
            algebraMap ℚ[X] (RatFunc ℚ) ((denominator m n).map (Int.castRingHom ℚ)) =
          algebraMap ℚ[X] (RatFunc ℚ) (H.map (Int.castRingHom ℚ))

open Matrix

private theorem u_zero {R : Type*} [CommRing R] (t : R) : (lucasU t 1 (0 : ℤ)) = 0 :=
  (lucas_recurrence t 1).1

private theorem u_one {R : Type*} [CommRing R] (t : R) : (lucasU t 1 (1 : ℤ)) = 1 :=
  (lucas_recurrence t 1).2.1

private theorem u_rec {R : Type*} [CommRing R] (t : R) (k : ℕ) :
    (lucasU t 1 ((k + 2 : ℕ) : ℤ)) = t * (lucasU t 1 ((k + 1 : ℕ) : ℤ)) - (lucasU t 1 (k : ℤ)) := by
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Units.val_one, one_mul]
    using (lucas_recurrence t 1).2.2 (k : ℤ)

private theorem u_doubling {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    (lucasU t 1 ((2*n : ℕ) : ℤ)) = 2 * (lucasU t 1 (n : ℤ)) * (lucasU t 1 ((n+1 : ℕ) : ℤ)) -
        t * (lucasU t 1 (n : ℤ)) ^ 2 ∧
    lucasU t 1 ((2*n+1 : ℕ) : ℤ) = (lucasU t 1 ((n+1 : ℕ) : ℤ))^2 - (lucasU t 1 (n : ℤ)) ^2 := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Units.val_one, one_mul] using (doubling t 1 (n : ℤ))

private theorem u_sum {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (2*n+1), (lucasU t 1 (k : ℤ))) = (lucasU t 1 ((n+1 : ℕ) : ℤ)) *
        ((lucasU t 1 ((n+1 : ℕ) : ℤ)) + (lucasU t 1 (n : ℤ))) := by
  induction n with
  | zero => simp [u_zero, u_one]
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega,
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    have h := u_doubling t (n+1)
    have he : (lucasU t 1 ((2*n+1+1 : ℕ) : ℤ)) = 2 * (lucasU t 1 ((n+1 : ℕ) : ℤ)) *
        (lucasU t 1 ((n+1+1 : ℕ) : ℤ)) - t * (lucasU t 1 ((n+1 : ℕ) : ℤ))^2 := by
      simpa only [show 2*n+1+1 = 2*(n+1) by omega] using h.1
    have ho : (lucasU t 1 ((2*n+1+1+1 : ℕ) : ℤ)) = (lucasU t 1 ((n+1+1 : ℕ) : ℤ))^2 -
        (lucasU t 1 ((n+1 : ℕ) : ℤ))^2 := by
      simpa only [show 2*n+1+1+1 = 2*(n+1)+1 by omega] using h.2
    rw [he, ho]
    linear_combination (lucasU t 1 ((n+1 : ℕ) : ℤ)) * u_rec t n


private theorem f_eq_lucas (j : ℕ) : fibonacciRecurrencePolynomial j =
    lucasU (X : ℤ[X]) (-1) (j : ℤ) := by
  induction j using Nat.twoStepInduction with
  | zero => exact (lucas_recurrence (X : ℤ[X]) (-1)).1.symm
  | one => exact (lucas_recurrence (X : ℤ[X]) (-1)).2.1.symm
  | more j h0 h1 =>
    rw [show fibonacciRecurrencePolynomial (j+2) = X * fibonacciRecurrencePolynomial (j+1) +
        fibonacciRecurrencePolynomial j from rfl, h0, h1]
    have h := (lucas_recurrence (X : ℤ[X]) (-1)).2.2 (j : ℤ)
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Units.val_neg,
      Units.val_one, neg_mul, one_mul, sub_neg_eq_add] using h.symm

private theorem even_step_reduction (m : ℕ) (hm : Even m) :
    ∃ t : ℤ[X], ∀ k : ℕ, fibonacciRecurrencePolynomial (m*k) =
        fibonacciRecurrencePolynomial m * (lucasU t 1 (k : ℤ)) := by
  let A : Matrix (Fin 2) (Fin 2) ℤ[X] := ↑(companion (X : ℤ[X]) (-1))
  let B := A ^ m
  have hA (j : ℕ) : (A ^ j) 1 0 = fibonacciRecurrencePolynomial j := by
    rw [f_eq_lucas]
    simp only [lucasU, zpow_natCast, Units.val_pow_eq_pow_val, A]
  have hdet : B.det = 1 := by
    simpa only [B, A, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg,
      Units.val_one, hm.neg_one_pow] using
      (D5.S1.Recurrence.LucasCompanion.companion_power_det (X : ℤ[X]) (-1) (m : ℤ))
  refine ⟨B.trace, ?_⟩
  intro k
  have hb (i : ℕ) : (B ^ i) 1 0 = fibonacciRecurrencePolynomial (m*i) := by
    rw [show B ^ i = A ^ (m*i) by simp only [B, pow_mul], hA]
  have hr (i : ℕ) : fibonacciRecurrencePolynomial (m*(i+2)) = B.trace *
      fibonacciRecurrencePolynomial (m*(i+1)) - fibonacciRecurrencePolynomial (m*i) := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ[X] => M 1 0)
      (D5.S0.Observation.MatrixTracePowerSum.pow_add_two B i)
    simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hdet, one_mul, hb] using h
  induction k using Nat.twoStepInduction with
  | zero => simp [u_zero, fibonacciRecurrencePolynomial]
  | one => simp [u_one]
  | more k h0 h1 => rw [hr, h1, h0, u_rec]; ring

private theorem denominator_top_coeff (m n : ℕ) (hm : 2 ≤ m) :
    (denominator m n).coeff (m*(2*n+1)-1) = 1 := by
  have hpos (k : ℕ) (hk : 1 ≤ k) : 0 < m*k := Nat.mul_pos (by omega) (by omega)
  have hdeg (k : ℕ) (hk : 1 ≤ k) : (fibonacciRecurrencePolynomial (m*k)).natDegree = m*k-1 := by
    have h := (D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients.fibonacci_recurrence_polynomial_coefficients).1 (m*k-1)
    simpa only [show m*k-1+1 = m*k by have := hpos k hk; omega] using h.1
  have hlead : (fibonacciRecurrencePolynomial (m*(2*n+1))).coeff (m*(2*n+1)-1) = 1 := by
    have h := (D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients.fibonacci_recurrence_polynomial_coefficients).1 (m*(2*n+1)-1)
    simpa only [show m*(2*n+1)-1+1 = m*(2*n+1) by have := hpos (2*n+1) (by omega); omega] using h.2
  classical
  rw [denominator, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (2*n+1)]
  · exact hlead
  · intro b hb hne
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [hdeg b (Finset.mem_Icc.mp hb).1]
    have hb' := (Finset.mem_Icc.mp hb).2
    have hp := hpos b (Finset.mem_Icc.mp hb).1
    have hp' := hpos (2*n+1) (by omega)
    have hlt : m*b < m*(2*n+1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  · intro hnot
    exact False.elim (hnot (by simp))


private theorem scaled_product_quotient {R : Type*} [CommRing R] (c t : R) (n : ℕ) :
    ∃ H : R, (∑ k ∈ Finset.Icc 1 (2*n+1), c * (lucasU t 1 (k : ℤ))) * H =
      ∏ k ∈ Finset.Icc 1 (2*n+1), c * (lucasU t 1 (k : ℤ)) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨1, by simp [u_one]⟩
  let W : R := ∏ k ∈ (Finset.Icc 1 (2*n)).erase (n+1), (lucasU t 1 (k : ℤ))
  refine ⟨c^(2*n) * ((lucasU t 1 ((n+1 : ℕ) : ℤ)) - (lucasU t 1 (n : ℤ))) * W, ?_⟩
  have hrestore : (lucasU t 1 ((n+1 : ℕ) : ℤ)) * W = ∏ k ∈ Finset.Icc 1 (2*n),
      (lucasU t 1 (k : ℤ)) := by
    exact Finset.mul_prod_erase (Finset.Icc 1 (2*n))
      (fun k : ℕ => lucasU t 1 (k : ℤ)) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hextend : (∏ k ∈ Finset.Icc 1 (2*n+1), (lucasU t 1 (k : ℤ))) =
      (∏ k ∈ Finset.Icc 1 (2*n), (lucasU t 1 (k : ℤ))) * lucasU t 1 ((2*n+1 : ℕ) : ℤ) := by
    exact Finset.prod_Icc_succ_top (by omega) _
  have hsum : (∑ k ∈ Finset.Icc 1 (2*n+1), c * (lucasU t 1 (k : ℤ))) =
      c * ((lucasU t 1 ((n+1 : ℕ) : ℤ)) * ((lucasU t 1 ((n+1 : ℕ) : ℤ)) +
          (lucasU t 1 (n : ℤ)))) := by
    rw [← Finset.mul_sum, u_sum]
  have hprod : (∏ k ∈ Finset.Icc 1 (2*n+1), c * (lucasU t 1 (k : ℤ))) =
      c^(2*n+1) * ∏ k ∈ Finset.Icc 1 (2*n+1), (lucasU t 1 (k : ℤ)) := by
    rw [Finset.prod_mul_distrib]
    simp
  rw [hsum, hprod, hextend, (u_doubling t n).2, ← hrestore, pow_succ]
  ring

private theorem polynomial_quotient (m n : ℕ) (hm : Even m) :
    ∃ H : ℤ[X], denominator m n * H = numerator m n := by
  obtain ⟨t, ht⟩ := even_step_reduction m hm
  obtain ⟨H, hH⟩ := scaled_product_quotient (fibonacciRecurrencePolynomial m) t n
  refine ⟨H, ?_⟩
  simpa only [denominator, numerator, ← ht] using hH

theorem result : claim := by
  intro m n hm he
  have hden : denominator m n ≠ 0 := by
    intro hz
    have h := denominator_top_coeff m n hm
    rw [hz, Polynomial.coeff_zero] at h
    exact zero_ne_one h
  obtain ⟨H, hH⟩ := polynomial_quotient m n he
  refine ⟨hden, H, ?_⟩
  let embed : ℤ[X] → RatFunc ℚ := fun p =>
    algebraMap ℚ[X] (RatFunc ℚ) (p.map (Int.castRingHom ℚ))
  have hinj : Function.Injective embed := by
    exact (RatFunc.algebraMap_injective ℚ).comp
      (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)
  have hne : algebraMap ℚ[X] (RatFunc ℚ) ((denominator m n).map (Int.castRingHom ℚ)) ≠ 0 := by
    intro hz
    apply hden
    apply hinj
    simpa only [embed, Polynomial.map_zero, map_zero] using hz
  apply (div_eq_iff hne).mpr
  have hh := congrArg embed hH
  simpa only [embed, Polynomial.map_mul, map_mul, mul_comm] using hh.symm

end D5.S3.ArithSums.BalaEvenStepFibonacciPolynomialIntegrality
