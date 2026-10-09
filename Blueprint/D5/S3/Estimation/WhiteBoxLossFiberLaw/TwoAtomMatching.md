# Two-Atom Coding Energy

## Abstract

Nonnegative two-atom coding admits an exact square completion and a radial lower bound.

**Theorem 1.1 (Code energy square completion).**

$$codeEnergy - radial = residualSquare + correlationDefect.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_energy_excess_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit direction and a real signal amplitude, the excess of the nonnegative two-atom code energy over the radial baseline is the sum of a squared residual and a correlation defect weighted by the regularization parameter. The identity keeps both code coordinates and both dictionary atoms in the same expression.

**Theorem 1.2 (Every feasible code obeys the radial lower bound).**

$$codeEnergy \ge lambda times norm - lambdaSquare.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.feasible_code_energy_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the signal norm is at least the regularization parameter, every coordinatewise nonnegative code has energy at least the radial baseline. The conclusion follows from the nonnegative square and the Cauchy--Schwarz correlation defects.

**Theorem 1.3 (The infimal code cost obeys the radial lower bound).**

$$codeCost \ge radial.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_cost_radial_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the infimum over all feasible nonnegative two-coordinate codes preserves the radial lower bound. The zero code supplies a nonempty family, while the pointwise square-completion inequality supplies the common floor.

**Theorem 1.4 (Separated target witnesses occupy different slots).**

$$separatedTargets \Rightarrow identityOrSwap.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.two_slot_matching_from_separate_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two target directions whose distance is at least twice the tolerance, if each target has a dictionary slot within the tolerance, the slots are distinct. Consequently the ordered dictionary matches the targets either in the identity order or after swapping its two entries.

## References

- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_cost_radial_lower_bound`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_energy_excess_eq`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.feasible_code_energy_lower_bound`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.two_slot_matching_from_separate_witnesses`
