/- GID: D5/S3/QuantumStates/PhaseLockedOverlap
   generality: G
   mirror-B: D5/B/S3/QuantumStates/PhaseLockedOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unit-phase conjugation locks an overlap to a rotated real line. -/

import Mathlib.Analysis.Complex.Basic

/- Library-search audit trail (2026-08-16):
   * D5 has no existing phase-line theorem for a complex overlap.
   * Two local `smart_search.sh` queries found no direct Mathlib declaration.
   * `Complex.inv_eq_conj` and `Complex.ofReal_eq_re_of_isSelfAdjoint` provide the exact
     unit-phase and real-line steps, and are applied below instead of being reproved. -/

namespace D5.S3.QuantumStates.PhaseLockedOverlap

/-- A complex overlap whose conjugate is locked by the inverse square of a unit phase lies on
that phase's rotated real line. This is the scalar core of the two-torsion overlap constraint. -/
theorem phase_locked_overlap_is_rotated_real
    (phase overlap : ℂ) (hphase : ‖phase‖ = 1)
    (hlock : star overlap = (phase⁻¹) ^ 2 * overlap) :
    ∃ r : ℝ, overlap = phase * r := by
  have hphase_ne : phase ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hphase
    norm_num at hphase
  have hconj_phase : star phase = phase⁻¹ := (Complex.inv_eq_conj hphase).symm
  have hconj_phase_inv : star (phase⁻¹) = phase := by
    rw [← hconj_phase, star_star]
  have hrotated : IsSelfAdjoint (phase⁻¹ * overlap) := by
    rw [isSelfAdjoint_iff]
    rw [star_mul', hconj_phase_inv, hlock]
    simp [pow_two, hphase_ne, mul_assoc]
  have hreal : ((phase⁻¹ * overlap).re : ℂ) = phase⁻¹ * overlap :=
    (Complex.ofReal_eq_re_of_isSelfAdjoint hrotated).mp rfl
  refine ⟨(phase⁻¹ * overlap).re, ?_⟩
  calc
    overlap = phase * (phase⁻¹ * overlap) := by
      rw [← mul_assoc, mul_inv_cancel₀ hphase_ne, one_mul]
    _ = phase * ((phase⁻¹ * overlap).re : ℂ) := by rw [hreal]

#print axioms phase_locked_overlap_is_rotated_real

end D5.S3.QuantumStates.PhaseLockedOverlap
