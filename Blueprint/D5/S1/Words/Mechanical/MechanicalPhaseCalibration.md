# Mechanical Phase Calibration

## Abstract

Joint slope and phase changes have an exact local mechanical-word error measure.

**Theorem 1.1 (Swept cuts and the least local phase error).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalPhaseCalibration.joint_phase_calibration_law`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalPhaseCalibration.joint_phase_calibration_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive horizon n, let g be a positive lower bound on the distances of the n cumulative rotation cuts from both endpoints and from one another. Assume that the original and perturbed slopes lie in [0,1). If every displacement u+k*delta, for k from zero through n, has absolute value at most g/4, then the set of phases in [0,1) where the two actual n-bit mechanical words differ has Lebesgue measure equal to the sum of those absolute displacements. The shifted phase itself can be any real number.

The proof identifies the cumulative floor changes with half-open intervals swept by their cuts and proves these intervals are pairwise disjoint. The time-zero cut contributes [1-u,1) for nonnegative u and [0,-u) for negative u. A nonzero cumulative change produces an actual word mismatch because n is positive and another cumulative coordinate remains unchanged.

If n*abs(delta) is at most g/4, the centered phase u=-n*delta/2 is permitted. Its error measure is abs(delta) times the integer floor of (n+1)^2/4. Pairing opposite indices proves that every other permitted phase has at least this error. The minimum is over the stated local phase class; the theorem does not extend that comparison to phase shifts outside the separation conditions.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalPhaseCalibration.joint_phase_calibration_law`
- Dependency: [D5/S1/Words/Mechanical/MechanicalSlopeSensitivity](MechanicalSlopeSensitivity.md)
