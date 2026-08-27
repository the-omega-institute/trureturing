/- GID: D5/S3/Quantum/Measurements/DeterministicReadoutPvm
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/DeterministicReadoutPvm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic readout fibers give orthogonal complete diagonal projections. -/

import Mathlib

open scoped BigOperators

noncomputable section

namespace D5.S3.Quantum.Measurements.DeterministicReadoutPvm

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {X O : Type*} [Fintype X] [Fintype O]
  [DecidableEq X] [DecidableEq O]

/- The projection is constructed from the source readout fiber, on the standard
   basis of the finite state carrier. -/
def deterministicProjection (readout : X → O) (outcome : O) : Matrix X X ℂ :=
  Matrix.diagonal (fun state => if readout state = outcome then 1 else 0)

theorem deterministic_readout_pvm (readout : X → O) :
    (∀ outcome outcome',
      deterministicProjection readout outcome *
          deterministicProjection readout outcome' =
        if outcome = outcome' then deterministicProjection readout outcome else 0) ∧
      (∑ outcome, deterministicProjection readout outcome =
        (1 : Matrix X X ℂ)) := by
  constructor
  · intro outcome outcome'
    rw [deterministicProjection, deterministicProjection,
      Matrix.diagonal_mul_diagonal]
    by_cases h : outcome = outcome'
    · subst outcome'
      simp
    · rw [if_neg h]
      apply Matrix.diagonal_eq_zero.mpr
      funext state
      by_cases hs : readout state = outcome <;>
        simp [hs, h]
  · ext state state'
    by_cases h : state = state'
    · subst state'
      rw [Matrix.sum_apply]
      simp only [deterministicProjection, Matrix.diagonal_apply_eq]
      rw [Fintype.sum_eq_single (readout state)]
      · simp
      · intro other hne
        simp [Ne.symm hne]
    · rw [Matrix.sum_apply]
      simp [deterministicProjection, h]

#print axioms deterministic_readout_pvm

end D5.S3.Quantum.Measurements.DeterministicReadoutPvm
