/- GID: D5/S1/Recurrence/Algebraic/ExponentialTranscendence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/ExponentialTranscendence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Exp, mathlib/module/Mathlib.LinearAlgebra.Eigenspace.Basic, mathlib/module/Mathlib.LinearAlgebra.DFinsupp, mathlib/module/Mathlib.RingTheory.Algebraic.Basic, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Polynomial independence of the formal variable and its exponential over the rationals. -/

import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.Ring

namespace D5.S1.Recurrence.Algebraic.ExponentialTranscendence

open Polynomial PowerSeries

private noncomputable abbrev D : Module.End ℚ (PowerSeries ℚ) :=
  (PowerSeries.derivative (R := ℚ)).toLinearMap

private theorem shifted_derivative (p : Polynomial ℚ) (j : ℕ) :
    (D - (j : ℚ) • 1) ((p : PowerSeries ℚ) * exp ℚ ^ j) =
      (p.derivative : PowerSeries ℚ) * exp ℚ ^ j := by
  have he : PowerSeries.derivative (exp ℚ ^ j) = (j : ℚ) • exp ℚ ^ j := by
    cases j with
    | zero => simp [PowerSeries.derivative_one]
    | succ j =>
      rw [PowerSeries.derivative_pow, PowerSeries.derivative_exp]
      simp only [Nat.add_sub_cancel]
      rw [Algebra.smul_def]
      simp only [map_natCast]
      rw [pow_succ]
      ring
  change PowerSeries.derivative ((p : PowerSeries ℚ) * exp ℚ ^ j) -
    (j : ℚ) • ((p : PowerSeries ℚ) * exp ℚ ^ j) = _
  rw [Derivation.leibniz, PowerSeries.derivative_coe, he]
  simp only [smul_eq_mul, mul_smul_comm]
  ring

private theorem shifted_derivative_pow (p : Polynomial ℚ) (j k : ℕ) :
    ((D - (j : ℚ) • 1) ^ k) ((p : PowerSeries ℚ) * exp ℚ ^ j) =
      ((Polynomial.derivative^[k] p : Polynomial ℚ) : PowerSeries ℚ) * exp ℚ ^ j := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, shifted_derivative, ih,
      Function.iterate_succ_apply]

private theorem polynomial_exp_mem (p : Polynomial ℚ) (j : ℕ) :
    (p : PowerSeries ℚ) * exp ℚ ^ j ∈ D.maxGenEigenspace (j : ℚ) := by
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨p.natDegree + 1, ?_⟩
  rw [LinearMap.mem_ker, shifted_derivative_pow,
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self p.natDegree)]
  simp

/-- Evaluate the first polynomial variable at the formal variable and the second at its
exponential. -/
noncomputable def exponentialEval : Polynomial (Polynomial ℚ) →+* PowerSeries ℚ :=
  Polynomial.eval₂RingHom Polynomial.coeToPowerSeries.ringHom (exp ℚ)

/-- No nonzero bivariate rational polynomial vanishes at the formal variable and its
exponential power series. -/
theorem exponentialEval_injective : Function.Injective exponentialEval := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  have hind : iSupIndep (fun j : ℕ => D.maxGenEigenspace (j : ℚ)) :=
    D.independent_maxGenEigenspace.comp Nat.cast_injective
  have hsum : ∑ j ∈ p.support, (p.coeff j : PowerSeries ℚ) * exp ℚ ^ j = 0 := by
    simpa only [exponentialEval, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      Polynomial.coeToPowerSeries.ringHom_apply] using hp
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind p.support
    (fun j => (p.coeff j : PowerSeries ℚ) * exp ℚ ^ j)
    (fun j _ => polynomial_exp_mem (p.coeff j) j) hsum
  apply Polynomial.ext
  intro j
  by_cases hj : j ∈ p.support
  · have hjzero := hzero j hj
    have he : exp ℚ ^ j ≠ 0 := pow_ne_zero _ (PowerSeries.isUnit_exp ℚ).ne_zero
    have hc : (p.coeff j : PowerSeries ℚ) = 0 := (mul_eq_zero.mp hjzero).resolve_right he
    simpa only [Polynomial.coeff_zero] using Polynomial.coe_eq_zero_iff.mp hc
  · simpa only [Polynomial.coeff_zero] using Polynomial.notMem_support_iff.mp hj

#print axioms exponentialEval_injective

/-- The exponential power series is transcendental over the polynomial ring in the
formal variable. -/
theorem exp_transcendental : Transcendental (Polynomial ℚ) (exp ℚ) := by
  rw [transcendental_iff_injective]
  change Function.Injective exponentialEval
  exact exponentialEval_injective

#print axioms exp_transcendental

end D5.S1.Recurrence.Algebraic.ExponentialTranscendence
