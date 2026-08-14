/- GID: D5/S3/QuantumBounds/TsirelsonTightness
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/TsirelsonTightness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify Bell-state attainment and the fixed CHSH trace-expectation maximum. -/

import D5.S3.QuantumBounds.CHSHWitness
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Algebra.Star.CHSH

/-!
# Tightness of the fixed CHSH witness

This module proves that `2 * Real.sqrt 2` is the greatest real trace expectation of the fixed
operator `CHSHWitness.chshOperator` over positive-semidefinite trace-one two-qubit states.

It proves no converse, no result for varying observables, and no claim beyond this fixed witness.
-/

namespace D5.S3.QuantumBounds.TsirelsonTightness

open scoped ComplexOrder MatrixOrder

/-- The Bell state attains the universal trace-expectation bound for the fixed CHSH operator. -/
theorem bell_chsh_state_expectation_is_greatest :
    IsGreatest
      (Set.range fun state :
        { rho : CHSHWitness.TwoQubitMatrix //
          rho.PosSemidef ∧ Matrix.trace rho = 1 } =>
        RCLike.re (Matrix.trace (state.1 * CHSHWitness.chshOperator)))
      (2 * Real.sqrt 2) := by
  constructor
  · refine ⟨⟨CHSHWitness.bellDensity, CHSHWitness.bell_density_is_state⟩, ?_⟩
    change RCLike.re (Matrix.trace
      (CHSHWitness.bellDensity * CHSHWitness.chshOperator)) = 2 * Real.sqrt 2
    rw [CHSHWitness.bell_chsh_value]
    norm_num
  · rintro _ ⟨state, rfl⟩
    have hchsh :
        CHSHWitness.chshOperator ≤
          Real.sqrt 2 ^ 3 • (1 : CHSHWitness.TwoQubitMatrix) := by
      rw [CHSHWitness.chsh_operator_eq_lifted_chsh]
      exact tsirelson_inequality
        CHSHWitness.liftA0 CHSHWitness.liftA1
        CHSHWitness.liftB0 CHSHWitness.liftB1
        CHSHWitness.lifted_observables_form_chsh_tuple
    have hpositive :
        (Real.sqrt 2 ^ 3 • (1 : CHSHWitness.TwoQubitMatrix) -
          CHSHWitness.chshOperator).PosSemidef :=
      hchsh
    have htrace := RHLinalg.trace_mul_nonneg_of_posSemidef state.property.1 hpositive
    simp only [mul_sub, Matrix.trace_sub, map_sub] at htrace
    have hscalar :
        RCLike.re (Matrix.trace
          (state.1 * (Real.sqrt 2 ^ 3 • (1 : CHSHWitness.TwoQubitMatrix)))) =
          2 * Real.sqrt 2 := by
      rw [Algebra.mul_smul_comm, mul_one, Matrix.trace_smul, state.property.2]
      norm_num [pow_succ]
    rw [hscalar] at htrace
    exact sub_nonneg.mp htrace

#print axioms bell_chsh_state_expectation_is_greatest

end D5.S3.QuantumBounds.TsirelsonTightness
