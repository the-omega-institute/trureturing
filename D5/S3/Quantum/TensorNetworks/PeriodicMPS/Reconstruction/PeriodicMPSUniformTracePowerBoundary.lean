/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTracePowerBoundary
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTracePowerBoundary
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Dickson power traces on traceless matrix pencils. -/
import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Dickson

/-!
# Trace-power formulas at the traceless boundary

The first-kind Dickson polynomial with parameter `D` gives the power trace of a
two-by-two matrix of determinant `D` when evaluated at its trace. At trace zero,
the odd power traces vanish and their derivative is `n * (-D)^((n - 1) / 2)`.
The matrix-curve formula allows the determinant to vary with the curve.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTracePowerBoundary

open Polynomial
open D5.S0.Observation.MatrixTracePowerSum (trace_pow_add_two)

variable {R : Type*} [CommRing R]

private theorem dickson_first_zero (D : R) : dickson 1 D 0 = 2 := by
  rw [dickson_zero, Nat.cast_one]
  ring

/-- The checked two-by-two matrix recurrence identifies its power traces with the
first-kind Dickson polynomials evaluated at the trace. -/
theorem trace_pow_eq_eval_dickson (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    (M ^ n).trace = (dickson 1 M.det n).eval M.trace := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [pow_zero, Matrix.trace_one, Fintype.card_fin, Nat.cast_two,
      dickson_first_zero, eval_ofNat]
  | one =>
    simp only [pow_one, dickson_one, eval_X]
  | more k ih0 ih1 =>
    simp only [trace_pow_add_two M k, dickson_add_two 1 M.det k, eval_sub, eval_mul,
      eval_X, eval_C, ih0, ih1]

private theorem recurrence_at_zero (T D : R[X]) (f : ℕ → R[X])
    (hzero : f 0 = 2) (hone : f 1 = T)
    (hstep : ∀ n, f (n + 2) = T * f (n + 1) - D * f n) (hT : T.eval 0 = 0)
    (m : ℕ) :
    (f (2 * m)).eval 0 = 2 * (-D.eval 0) ^ m ∧
      (f (2 * m + 1)).eval 0 = 0 ∧
        (f (2 * m + 1)).derivative.eval 0 =
          ((2 * m + 1 : ℕ) : R) * (-D.eval 0) ^ m * T.derivative.eval 0 := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Nat.mul_zero, Nat.zero_add, hzero, hone, eval_ofNat, hT, pow_zero,
        mul_one, Nat.cast_one, one_mul]
  | succ m ih =>
    obtain ⟨heven, hodd, hderiv⟩ := ih
    have evenStep : f (2 * (m + 1)) = T * f (2 * m + 1) - D * f (2 * m) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega]
      exact hstep (2 * m)
    have oddStep : f (2 * (m + 1) + 1) = T * f (2 * (m + 1)) - D * f (2 * m + 1) := by
      calc
        f (2 * (m + 1) + 1) = f ((2 * m + 1) + 2) := congrArg f (by omega)
        _ = T * f ((2 * m + 1) + 1) - D * f (2 * m + 1) := hstep (2 * m + 1)
        _ = _ := by rw [show (2 * m + 1) + 1 = 2 * (m + 1) by omega]
    have evenValue : (f (2 * (m + 1))).eval 0 = 2 * (-D.eval 0) ^ (m + 1) := by
      rw [evenStep]
      simp only [eval_sub, eval_mul, hT, heven, pow_succ, zero_mul, zero_sub]
      ring
    refine ⟨evenValue, ?_, ?_⟩
    · rw [oddStep]
      simp only [eval_sub, eval_mul, hT, hodd, zero_mul, mul_zero, sub_self]
    · rw [oddStep]
      simp only [derivative_sub, derivative_mul, eval_sub, eval_add, eval_mul, hT, hodd,
        evenValue, hderiv, mul_zero, pow_succ, Nat.cast_add, Nat.cast_mul,
        Nat.cast_one, Nat.cast_two]
      ring

private theorem dickson_at_trace_zero (D : R) (m : ℕ) :
    (dickson 1 D (2 * m)).eval 0 = 2 * (-D) ^ m ∧
      (dickson 1 D (2 * m + 1)).eval 0 = 0 ∧
        (dickson 1 D (2 * m + 1)).derivative.eval 0 = ((2 * m + 1 : ℕ) : R) * (-D) ^ m := by
  simpa only [eval_C, derivative_X, eval_one, mul_one] using
    recurrence_at_zero (X : R[X]) (C D) (dickson 1 D) (dickson_first_zero D)
      (dickson_one 1 D) (dickson_add_two 1 D) eval_X m

/-- The even-period power trace at trace zero, including period zero. -/
theorem eval_dickson_even_at_trace_zero (D : R) (m : ℕ) :
    (dickson 1 D (2 * m)).eval 0 = 2 * (-D) ^ m :=
  (dickson_at_trace_zero D m).1

/-- Odd-period power traces vanish at trace zero for every determinant. -/
theorem eval_dickson_odd_at_trace_zero (D : R) (n : ℕ) (hn : Odd n) :
    (dickson 1 D n).eval 0 = 0 := by
  obtain ⟨m, rfl⟩ := hn.exists_bit1
  exact (dickson_at_trace_zero D m).2.1

/-- The derivative with respect to trace at fixed determinant for every odd period. -/
theorem derivative_dickson_odd_at_trace_zero (D : R) (n : ℕ) (hn : Odd n) :
    (dickson 1 D n).derivative.eval 0 = (n : R) * (-D) ^ ((n - 1) / 2) := by
  obtain ⟨m, rfl⟩ := hn.exists_bit1
  simpa only [show (2 * m + 1 - 1) / 2 = m by omega] using
    (dickson_at_trace_zero D m).2.2

/-- At a nonzero determinant, trace zero is a simple root of every odd-period power
trace over a characteristic-zero domain. -/
theorem rootMultiplicity_dickson_odd_at_trace_zero [IsDomain R] [CharZero R]
    (D : R) (hD : D ≠ 0) (n : ℕ) (hn : Odd n) :
    (dickson 1 D n).rootMultiplicity 0 = 1 := by
  obtain ⟨m, rfl⟩ := hn.exists_bit1
  have hroot : (dickson 1 D (2 * m + 1)).IsRoot 0 := (dickson_at_trace_zero D m).2.1
  have hderiv : ¬ (dickson 1 D (2 * m + 1)).derivative.IsRoot 0 := by
    change (dickson 1 D (2 * m + 1)).derivative.eval 0 ≠ 0
    rw [(dickson_at_trace_zero D m).2.2]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pow_ne_zero _ (neg_ne_zero.mpr hD))
  have hnonzero : dickson 1 D (2 * m + 1) ≠ 0 := by
    intro h
    apply hderiv
    simp only [h, derivative_zero, IsRoot, eval_zero]
  have hpos := (rootMultiplicity_pos hnonzero).2 hroot
  have hle : ¬ 1 < (dickson 1 D (2 * m + 1)).rootMultiplicity 0 :=
    fun h => hderiv ((one_lt_rootMultiplicity_iff_isRoot hnonzero).mp h).2
  omega

/-- The odd-period power trace of a polynomial matrix curve vanishes at a traceless
point. Its first derivative depends on the derivative of the trace and the value
of the determinant there. -/
theorem trace_pow_odd_at_traceless_curve (M : Matrix (Fin 2) (Fin 2) R[X])
    (htrace : M.trace.eval 0 = 0) (n : ℕ) (hn : Odd n) :
    ((M ^ n).trace).eval 0 = 0 ∧
      ((M ^ n).trace).derivative.eval 0 =
        (n : R) * (-M.det.eval 0) ^ ((n - 1) / 2) * M.trace.derivative.eval 0 := by
  obtain ⟨m, rfl⟩ := hn.exists_bit1
  have h := recurrence_at_zero M.trace M.det (fun k => (M ^ k).trace)
    (by simp only [pow_zero, Matrix.trace_one, Fintype.card_fin, Nat.cast_two])
    (by simp only [pow_one]) (trace_pow_add_two M) htrace m
  simpa only [show (2 * m + 1 - 1) / 2 = m by omega] using h.2

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTracePowerBoundary
