# Mechanical Slope Sensitivity

## Abstract

Finite numerical slope precision has an exact local cost in actual binary observations.

**Definition 1.1 (Actual word disagreement phases).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.slopeDisagreement`

*Formalization.* `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.slopeDisagreement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the subset of the unit phase interval at which the existing lowerMechanicalWord observations disagree at some time before n. The slope is perturbed while the initial phase and the convention for floor boundaries are held fixed.

**Theorem 1.2 (Constructed chamber, exact measure, and correlated bit changes).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.local_slope_disagreement_law`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.local_slope_disagreement_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every irrational slope strictly between zero and one and every finite horizon, the proof constructs a positive radius using actual distances between its cuts and from the relevant endpoints. Every nonnegative perturbation inside it gives an exact disagreement set: the disjoint swept intervals [1-fract(k*alpha)-k*delta,1-fract(k*alpha)), for k=1 through n. Their Lebesgue measure is delta*n*(n+1)/2. On the k-th interval the actual letter changes by +1 at time k-1, by -1 at time k when that position is observed, and by zero elsewhere. Irrationality, floor carries, interval separation, and measure additivity are derived in the live proof; no noise-region or measure certificate is assumed. The approximating slope need not be irrational. This is a local parameter-sensitivity theorem, not a global error law or an independent bit-noise model.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.local_slope_disagreement_law`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.slopeDisagreement`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](MechanicalBalance.md)
