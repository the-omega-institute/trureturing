/- GID: D5/S3/Weil/CayleyLaguerre/UnimodularTransferChebyshevIdentity
   generality: G
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/UnimodularTransferChebyshevIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify unimodular two-by-two transfer power traces with Chebyshev values. -/

import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Tactic

/-!
Library-search audit trail (2026-09-03):
* Exact D5 searches for a complex special-linear matrix trace-power identity with
  first-kind Chebyshev values found no whole-statement owner.
* `MatrixTracePowerSum.trace_pow_eq_add_pow` supplies the canonical frozen
  trace-power step for a two-by-two matrix from its determinant and trace.
* Pinned Mathlib has no exact matrix theorem, but
  `Polynomial.dickson_one_one_eval_add_inv` and
  `Polynomial.dickson_one_one_eq_chebyshev_T` supply the exact polynomial bridge.
* Searches of the other installed Lean packages found no exact theorem with this
  matrix carrier and these two identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped MatrixGroups

namespace D5.S3.Weil.CayleyLaguerre.UnimodularTransferChebyshevIdentity

/-- For every complex two-by-two determinant-one matrix, half the trace of its
`N`th power is the first-kind Chebyshev polynomial at half its trace. Consequently,
the corresponding Chebyshev slack is minus one quarter of the squared-trace
expression. -/
theorem unimodular_transfer_chebyshev_identities
    (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (N : Nat) :
    let x : Complex :=
      (1 / 2 : Complex) * Matrix.trace (M : Matrix (Fin 2) (Fin 2) Complex)
    (1 / 2 : Complex) *
          Matrix.trace ((M : Matrix (Fin 2) (Fin 2) Complex) ^ N) =
        (Polynomial.Chebyshev.T Complex (N : Int)).eval x /\
      1 - (Polynomial.Chebyshev.T Complex (N : Int)).eval x ^ 2 =
        -(1 / 4 : Complex) *
          (Matrix.trace ((M : Matrix (Fin 2) (Fin 2) Complex) ^ N) ^ 2 - 4) := by
  dsimp only
  let A : Matrix (Fin 2) (Fin 2) Complex := M
  let t : Complex := Matrix.trace A
  let p : Polynomial Complex :=
    Polynomial.C 1 * Polynomial.X ^ 2 +
      Polynomial.C (-t) * Polynomial.X + Polynomial.C 1
  have hpDegree : p.degree = 2 := by
    dsimp [p]
    exact Polynomial.degree_quadratic (by norm_num)
  have hpPositive : 0 < p.degree := by
    rw [hpDegree]
    norm_num
  obtain ⟨a, ha⟩ := Complex.exists_root hpPositive
  have haeq : a ^ 2 + -(t * a) + 1 = 0 := by
    simpa [p, Polynomial.IsRoot] using ha
  have hane : a ≠ 0 := by
    intro h
    subst a
    norm_num at haeq
  have hsum : t = a + a⁻¹ := by
    apply mul_right_cancel₀ hane
    rw [add_mul, inv_mul_cancel₀ hane]
    linear_combination -haeq
  have hpower : Matrix.trace (A ^ N) = a ^ N + (a⁻¹) ^ N := by
    apply D5.S0.Observation.MatrixTracePowerSum.trace_pow_eq_add_pow A a a⁻¹ hsum
    · simp [A, hane]
  have hdickson :
      (Polynomial.dickson 1 (1 : Complex) N).eval t = a ^ N + (a⁻¹) ^ N := by
    rw [hsum]
    exact Polynomial.dickson_one_one_eval_add_inv a a⁻¹ (by simp [hane]) N
  have hchebyshev :
      (Polynomial.dickson 1 (1 : Complex) N).eval t =
        2 * (Polynomial.Chebyshev.T Complex (N : Int)).eval ((1 / 2 : Complex) * t) := by
    rw [Polynomial.dickson_one_one_eq_chebyshev_T]
    simp [invOf_eq_inv]
  have hidentity :
      (1 / 2 : Complex) * Matrix.trace (A ^ N) =
        (Polynomial.Chebyshev.T Complex (N : Int)).eval ((1 / 2 : Complex) * t) := by
    rw [hpower, ← hdickson, hchebyshev]
    ring
  constructor
  · simpa [A, t] using hidentity
  · rw [← hidentity]
    ring

-- The public theorem has no propositional hypotheses.
example : True := trivial

-- The source matrix carrier has a concrete determinant-one inhabitant.
example : Matrix.SpecialLinearGroup (Fin 2) Complex := 1

-- The source degree carrier includes its endpoint.
example : Nat := 0

#print axioms unimodular_transfer_chebyshev_identities

end D5.S3.Weil.CayleyLaguerre.UnimodularTransferChebyshevIdentity
