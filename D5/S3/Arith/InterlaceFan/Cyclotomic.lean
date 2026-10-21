/- GID: D5/S3/Arith/InterlaceFan/Cyclotomic
   generality: G
   mirror-B: D5/B/S3/Arith/InterlaceFan/Cyclotomic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex, mathlib/module/Mathlib.NumberTheory.Cyclotomic.Basic, mathlib/module/Mathlib.RingTheory.Polynomial.Cyclotomic.Roots, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Cosine evaluation, order-class propagation, and Ramanujan witnesses for the interlace fan. -/

import D5.S3.Arith.InterlaceFan.Defs
import D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

noncomputable section

open Finset Polynomial
open scoped BigOperators Nat Real

namespace D5.S3.Arith.InterlaceFan.Cyclotomic

open D5.S3.Arith.InterlaceFan.Defs
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity

/- The real evaluation of the palindromic Fourier polynomial at the j-th
   root.  Writing it as a real sum keeps the sigma-coordinate convention
   explicit and avoids a hidden choice of the middle coefficient. -/
def evalCos (n j : ℕ) (x : Fin (n / 2) → ℝ) : ℝ :=
  ∑ k : Fin (n / 2), 2 * Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k

/- The factor two in `evalCos` is the pair of reciprocal monomials; `I` is
   the negative half of this real evaluation. -/
theorem I_eq_eval (n j : ℕ) (x : Fin (n / 2) → ℝ) :
    I n j x = -(1 / 2 : ℝ) * evalCos n j x := by
  simp only [I, evalCos]
  change (∑ k : Fin (n / 2),
      -Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k) =
    (-(1 / 2 : ℝ)) • ∑ k : Fin (n / 2),
      2 * Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k
  rw [Finset.smul_sum (s := (Finset.univ : Finset (Fin (n / 2))))]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring


/-- The reciprocal polynomial in the pinned sigma coordinates. -/
def sigmaPoly {R : Type*} [CommRing R] (n : ℕ) (x : Fin (n / 2) → R) : R[X] :=
  ∑ k : Fin (n / 2), Polynomial.C (x k) *
    (Polynomial.X ^ ((k : ℕ) + 1) + Polynomial.X ^ (n - ((k : ℕ) + 1)))

/-- The standard primitive root of unity. -/
def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

private lemma zeta_pow (n j m : ℕ) :
    (zeta n ^ j) ^ m = Complex.exp
      ((2 * Real.pi * j * m / n : ℝ) * Complex.I) := by
  simp only [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma reciprocal_pair (n j m : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    (zeta n ^ j) ^ m + (zeta n ^ j) ^ (n - m) =
      (2 * Real.cos (2 * Real.pi * j * m / n) : ℝ) := by
  have hz := Complex.isPrimitiveRoot_exp n hn.ne'
  have hz0 : zeta n ^ j ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hzn : (zeta n ^ j) ^ n = 1 := by
    rw [← pow_mul, mul_comm j n, pow_mul]
    simpa [zeta] using congrArg (fun z : ℂ => z ^ j) hz.pow_eq_one
  rw [pow_sub₀ _ hz0 hm, hzn, one_mul, zeta_pow, ← Complex.exp_neg]
  have hc := Complex.two_cos ((2 * Real.pi * j * m / n : ℝ) : ℂ)
  push_cast at hc ⊢
  rw [show -((2 * (Real.pi : ℂ) * j * m / n) * Complex.I) =
    -(2 * (Real.pi : ℂ) * j * m / n) * Complex.I by ring]
  simpa using hc.symm

/-- Evaluation of the reciprocal polynomial is the real cosine sum. -/
theorem I_eq_eval_poly (n j : ℕ) (x : Fin (n / 2) → ℝ) :
    ((sigmaPoly n x).map Complex.ofRealHom).eval (zeta n ^ j) =
      (evalCos n j x : ℂ) := by
  classical
  simp only [sigmaPoly, Polynomial.map_sum, Polynomial.eval_finsetSum,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, evalCos,
    Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt := k.isLt
  rw [reciprocal_pair n j ((k : ℕ) + 1) (by omega) (by omega)]
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  ring

end D5.S3.Arith.InterlaceFan.Cyclotomic
