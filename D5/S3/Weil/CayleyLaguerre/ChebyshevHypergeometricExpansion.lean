/- GID: D5/S3/Weil/CayleyLaguerre/ChebyshevHypergeometricExpansion
   generality: G
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/ChebyshevHypergeometricExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Shifted Chebyshev polynomials have their terminating hypergeometric expansion. -/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-! Library-search audit trail (2026-09-01):
   * The target atom remains in `residual-open` with empty `coverage_gids`, and its atom id has
     no formalization receipt.
   * Repository searches for shifted Chebyshev, Pochhammer, and hypergeometric expansions found
     no existing coefficient theorem. `CayleyMomentTransport.chebyshev_stieltjes_jet` and
     `LaguerreChebyshevDuality.laguerre_chebyshev_duality` instead take this expansion as a
     hypothesis.
   * Pinned Mathlib has no exact shifted-Chebyshev hypergeometric formula.
     `Polynomial.Chebyshev.iterate_derivative_T_eval_one_recurrence`, polynomial Taylor
     expansion, and `Polynomial.ascPochhammer_succ_eval` provide the proof below.
   * The installed third-party Lean packages contain no Chebyshev/Pochhammer or shifted
     Chebyshev/hypergeometric theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Polynomial

namespace D5.S3.Weil.CayleyLaguerre.ChebyshevHypergeometricExpansion

/-- The shifted first-kind Chebyshev polynomial `P_n(X) = T_n(1 - 2X)`. -/
def shiftedChebyshev (n : Nat) : Real[X] :=
  (Polynomial.Chebyshev.T Real (n : Int)).comp (1 - 2 * X)

private theorem hypergeometric_coefficient_eq_derivative_coefficient (n k : Nat) :
    (ascPochhammer Real k).eval (-(n : Real)) *
          (ascPochhammer Real k).eval (n : Real) /
        ((ascPochhammer Real k).eval (1 / 2 : Real) * (k.factorial : Real)) =
      (-2 : Real) ^ k / (k.factorial : Real) *
        (derivative^[k] (Polynomial.Chebyshev.T Real (n : Int))).eval 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hHalfPositive : 0 < (ascPochhammer Real k).eval (1 / 2 : Real) :=
        ascPochhammer_pos k (1 / 2 : Real) (by positivity)
      have hHalfStepPositive : 0 < (1 / 2 : Real) + k := by positivity
      have hFactorial : (k.factorial : Real) ≠ 0 := by positivity
      have hSuccessor : ((k + 1 : Nat) : Real) ≠ 0 := by positivity
      have hDerivative :=
        Polynomial.Chebyshev.iterate_derivative_T_eval_one_recurrence
          (R := Real) (n : Int) k
      push_cast at hDerivative
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval,
        ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, pow_succ]
      field_simp [hHalfPositive.ne', hHalfStepPositive.ne', hFactorial, hSuccessor] at ih ⊢
      linear_combination (norm := ring_nf)
        ((k : Real) ^ 2 - (n : Real) ^ 2) * ih +
          ((ascPochhammer Real k).eval (1 / 2 : Real) * (-2 : Real) ^ k) * hDerivative

/-- The terminating hypergeometric expansion
`T_n(1 - 2x) = sum_k (-n)_k (n)_k / ((1/2)_k k!) x^k`. -/
theorem shifted_chebyshev_hypergeometric_expansion (n : Nat) (x : Real) :
    (shiftedChebyshev n).eval x =
      Finset.sum (Finset.range (n + 1)) (fun k =>
        ((ascPochhammer Real k).eval (-(n : Real)) *
            (ascPochhammer Real k).eval (n : Real) /
          ((ascPochhammer Real k).eval (1 / 2 : Real) * (k.factorial : Real))) * x ^ k) := by
  simp only [shiftedChebyshev, eval_comp, eval_sub, eval_one, eval_mul, eval_ofNat,
    eval_X]
  have hDegree :
      (Polynomial.taylor (1 : Real)
        (Polynomial.Chebyshev.T Real (n : Int))).natDegree < n + 1 := by
    simp [Polynomial.Chebyshev.natDegree_T]
  calc
    (Polynomial.Chebyshev.T Real (n : Int)).eval (1 - 2 * x) =
        (Polynomial.taylor (1 : Real)
          (Polynomial.Chebyshev.T Real (n : Int))).eval (-2 * x) := by
      rw [Polynomial.taylor_eval]
      congr 1
      ring
    _ = Finset.sum (Finset.range (n + 1)) (fun k =>
        (Polynomial.taylor (1 : Real)
          (Polynomial.Chebyshev.T Real (n : Int))).coeff k * (-2 * x) ^ k) := by
      exact Polynomial.eval_eq_sum_range' hDegree (-2 * x)
    _ = Finset.sum (Finset.range (n + 1)) (fun k =>
        ((ascPochhammer Real k).eval (-(n : Real)) *
            (ascPochhammer Real k).eval (n : Real) /
          ((ascPochhammer Real k).eval (1 / 2 : Real) * (k.factorial : Real))) * x ^ k) := by
      apply Finset.sum_congr rfl
      intro k _
      have hFactorial : (k.factorial : Real) ≠ 0 := by positivity
      have hDerivative :
          (k.factorial : Real) *
              (Polynomial.taylor (1 : Real)
                (Polynomial.Chebyshev.T Real (n : Int))).coeff k =
            (derivative^[k] (Polynomial.Chebyshev.T Real (n : Int))).eval 1 := by
        rw [Polynomial.taylor_coeff]
        have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := Real) (k := k))
          (Polynomial.Chebyshev.T Real (n : Int))
        simpa [nsmul_eq_mul] using congrArg (fun p : Real[X] => p.eval 1) h
      rw [mul_pow]
      calc
        (Polynomial.taylor (1 : Real)
              (Polynomial.Chebyshev.T Real (n : Int))).coeff k *
            ((-2 : Real) ^ k * x ^ k) =
            ((Polynomial.taylor (1 : Real)
                (Polynomial.Chebyshev.T Real (n : Int))).coeff k * (-2 : Real) ^ k) *
              x ^ k := by ring
        _ = ((ascPochhammer Real k).eval (-(n : Real)) *
                (ascPochhammer Real k).eval (n : Real) /
              ((ascPochhammer Real k).eval (1 / 2 : Real) * (k.factorial : Real))) *
            x ^ k := by
          congr 1
          rw [hypergeometric_coefficient_eq_derivative_coefficient n k]
          field_simp [hFactorial]
          nlinarith

#print axioms shifted_chebyshev_hypergeometric_expansion

end D5.S3.Weil.CayleyLaguerre.ChebyshevHypergeometricExpansion
