/- GID: D5/S3/Quantum/Measurements/ComputationalBasisKernelPreservation
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/ComputationalBasisKernelPreservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Basis fiber projectors preserve the deterministic readout kernel. -/

import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

/- Library-search audit trail (2026-08-27):
   * Body-shape search for coordinate rank-one projectors found the canonical
     `ProjectedUnistochasticDynamics.basisProjector`, which is imported rather
     than redeclared. Searches found no D5 theorem relating its fiber sums to a
     deterministic readout kernel.
   * Pinned Mathlib's exact `Matrix.trace_single_mul` computes the Born trace of
     a coordinate projector against a fiber sum. No end-to-end theorem was found. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Measurements.ComputationalBasisKernelPreservation

open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The rank-one density matrix of a computational-basis state reads one on
exactly its deterministic outcome fiber. Consequently, two basis states have
equal probabilities for every outcome exactly when the original readout agrees. -/
theorem computational_basis_kernel_preservation
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [DecidableEq Outcome] (q : State -> Outcome) (x y : State) :
    let rho : State -> Matrix State State ℂ := basisProjector
    let fiberProjector : Outcome -> Matrix State State ℂ := fun outcome =>
      ∑ state ∈ Finset.univ.filter (fun state => q state = outcome),
        basisProjector state
    (forall outcome,
      Matrix.trace (rho x * fiberProjector outcome) =
        if q x = outcome then 1 else 0) /\
      (q x = q y <->
        forall outcome,
          Matrix.trace (rho x * fiberProjector outcome) =
            Matrix.trace (rho y * fiberProjector outcome)) := by
  classical
  dsimp only
  have probability (state : State) (outcome : Outcome) :
      Matrix.trace
          (basisProjector state *
            ∑ z ∈ Finset.univ.filter (fun z => q z = outcome),
              basisProjector z) =
        if q state = outcome then 1 else 0 := by
    rw [show basisProjector state = Matrix.single state state 1 by rfl]
    rw [Matrix.trace_single_mul]
    simp only [one_smul]
    rw [Matrix.sum_apply]
    by_cases hreadout : q state = outcome <;>
      simp [hreadout, basisProjector, Matrix.single_apply]
  constructor
  · exact probability x
  · constructor
    · intro hxy outcome
      rw [probability x outcome, probability y outcome, hxy]
    · intro probabilities
      by_contra hxy
      have atX := probabilities (q x)
      rw [probability x (q x), probability y (q x)] at atX
      simp [Ne.symm hxy] at atX

#print axioms computational_basis_kernel_preservation

end D5.S3.Quantum.Measurements.ComputationalBasisKernelPreservation
