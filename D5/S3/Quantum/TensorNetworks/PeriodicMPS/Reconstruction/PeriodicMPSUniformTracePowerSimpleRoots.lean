/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTracePowerSimpleRoots
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTracePowerSimpleRoots
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Simple roots of the trace-one power polynomial. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTraceBase
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTracePowerBoundary
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-! The trace-one determinant polynomial has simple roots at every period `n ≥ 2`. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTracePowerSimpleRoots

open Polynomial
open scoped Matrix
open PeriodicMPSUniformTraceBase (normalizedTracePower)
open PeriodicMPSUniformTracePowerBoundary (trace_pow_eq_eval_dickson)

private theorem normalizedTracePower_comp (n : ℕ) :
    (normalizedTracePower n).comp (X * (1 - X)) = X ^ n + (1 - X) ^ n := by
  let d : Fin 2 → ℂ[X] := ![X, 1 - X]
  have htrace : (Matrix.diagonal d).trace = 1 := by
    simp [d, Matrix.trace_diagonal, Fin.sum_univ_two]
  have hdet : (Matrix.diagonal d).det = X * (1 - X) := by
    simp [d, Matrix.det_diagonal, Fin.prod_univ_two]
  calc
    (normalizedTracePower n).comp (X * (1 - X)) =
        (dickson 1 (X * (1 - X) : ℂ[X]) n).eval 1 := by
      let f : ℂ[X] →+* ℂ[X] := compRingHom (X * (1 - X))
      have hf : f X = X * (1 - X) := X_comp
      have h := eval_map_apply (p := dickson 1 (X : ℂ[X]) n) f 1
      rw [map_dickson, map_one, hf] at h
      exact h.symm
    _ = ((Matrix.diagonal d) ^ n).trace := by
      rw [trace_pow_eq_eval_dickson, htrace, hdet]
    _ = X ^ n + (1 - X) ^ n := by
      rw [Matrix.diagonal_pow, Matrix.trace_diagonal, Fin.sum_univ_two]
      simp [d]

private theorem exists_trace_one_pair (a : ℂ) : ∃ z : ℂ, z * (1 - z) = a := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (1 / 4 - a) (n := 2) zero_lt_two
  refine ⟨1 / 2 + t, ?_⟩
  linear_combination -ht

private theorem eval_derivative_normalizedTracePower_ne_zero (n : ℕ) (hn : 2 ≤ n)
    (a : ℂ) (ha : (normalizedTracePower n).IsRoot a) :
    (normalizedTracePower n).derivative.eval a ≠ 0 := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨z, hz⟩ := exists_trace_one_pair a
  have hzEval : (X * (1 - X) : ℂ[X]).eval z = a := by
    simpa only [eval_mul, eval_sub, eval_one, eval_X] using hz
  have haEval : (normalizedTracePower n).eval a = 0 := ha
  have hvalue : z ^ n + (1 - z) ^ n = 0 := by
    have h := congrArg (Polynomial.eval z) (normalizedTracePower_comp n).symm
    simpa only [eval_comp, hzEval, haEval, eval_add, eval_pow, eval_sub, eval_one, eval_X] using h
  intro hderivative
  have hdiff : (n : ℂ) * (z ^ (n - 1) - (1 - z) ^ (n - 1)) = 0 := by
    calc
      _ = (X ^ n + (1 - X : ℂ[X]) ^ n).derivative.eval z := by
        simp only [derivative_add, derivative_pow, derivative_sub, derivative_one, derivative_X,
          eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_zero, eval_X, mul_one]
        ring
      _ = ((normalizedTracePower n).comp (X * (1 - X))).derivative.eval z :=
        congrArg (fun p : ℂ[X] => p.derivative.eval z) (normalizedTracePower_comp n).symm
      _ = 0 := by
        rw [derivative_comp, eval_mul, eval_comp, hzEval, hderivative, mul_zero]
  have hpowers : z ^ (n - 1) = (1 - z) ^ (n - 1) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (Nat.cast_ne_zero.mpr hn0))
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hzero : (1 - z) ^ (n - 1) = 0 := by
    calc
      _ = (1 - z) ^ (n - 1) * (z + (1 - z)) := by
        rw [show z + (1 - z) = 1 by ring, mul_one]
      _ = z ^ (n - 1) * z + (1 - z) ^ (n - 1) * (1 - z) := by rw [hpowers, mul_add]
      _ = z ^ n + (1 - z) ^ n := by rw [← pow_succ, ← pow_succ, hsucc]
      _ = 0 := hvalue
  have hz_ne_one : z ≠ 1 := by
    intro h
    rw [h, one_pow, sub_self, zero_pow hn0, add_zero] at hvalue
    exact one_ne_zero hvalue
  exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hz_ne_one)) hzero

/-- Every root of the trace-one determinant trace-power polynomial has multiplicity one. -/
theorem rootMultiplicity_normalizedTracePower (n : ℕ) (hn : 2 ≤ n) (a : ℂ)
    (ha : (normalizedTracePower n).IsRoot a) :
    (normalizedTracePower n).rootMultiplicity a = 1 := by
  have hderivative := eval_derivative_normalizedTracePower_ne_zero n hn a ha
  have hnonzero : normalizedTracePower n ≠ 0 := by
    intro h
    exact hderivative (by rw [h, derivative_zero, eval_zero])
  have hpos := (rootMultiplicity_pos hnonzero).2 ha
  have hnot : ¬ 1 < (normalizedTracePower n).rootMultiplicity a :=
    fun h => hderivative ((one_lt_rootMultiplicity_iff_isRoot hnonzero).mp h).2
  omega

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTracePowerSimpleRoots
