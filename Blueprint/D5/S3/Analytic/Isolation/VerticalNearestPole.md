# Vertical isolation of a nearest point

## Abstract

A small vertical displacement isolates a nearest spectral point.

**Theorem 1.1 (An isolated nearest point after an arbitrarily small displacement).**

Lean statement: `D5/S3/Analytic/Isolation/VerticalNearestPole.isolated_nearest_of_vertical_perturbation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/VerticalNearestPole.isolated_nearest_of_vertical_perturbation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a complex spectrum is locally discrete in the positive half-plane and lies strictly to the left of a vertical line. Fix a radius smaller than the line's real coordinate, and a spectral point whose horizontal distance from the line is smaller than that radius. For any positive tolerance, one can move the center vertically by less than that tolerance and choose a disk of at most the fixed radius containing exactly one spectral point.

Only finitely many spectral points can meet a slightly enlarged compact disk. Each distinct pair has at most one equidistant height on the line. Avoiding this finite set of heights makes the nearest point unique, and its distance is strictly smaller than the next distance and the allowed radius.

This is a geometric selection theorem. It does not assert analytic continuation or pole residues.

**Theorem 1.2 (A free disk or an isolated real point).**

Lean statement: `D5/S3/Analytic/Isolation/VerticalNearestPole.real_center_spectral_dichotomy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/VerticalNearestPole.real_center_spectral_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive threshold below the real coordinate of the center, and assume that some spectral point lies to the right of that threshold. Either a disk around the real center is free of spectral points while another point is horizontally closer than its radius, or the unique closest point is real and lies to the right of the threshold.

In the second case a slightly larger disk contains only that real point. Both radii are bounded by the difference between the center and the threshold. The conclusion concerns locations only, with analytic and residue information left to the corresponding functions.

**Theorem 1.3 (Regularization at one preserves nonzero actual zero poles).**

Lean statement: `D5/S3/Analytic/Isolation/VerticalNearestPole.regularized_positive_log_family`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/VerticalNearestPole.regularized_positive_log_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the family members be entire and nonzero at one, with positive real weights. Subtract the affine normalization of their logarithmic derivative sum so that its numerator vanishes at one. Taking its analytic divided difference at one and dividing by the negative coordinate produces a continuation with the artificial pole at one removed. It is analytic at every nonzero point where all family members are nonzero. At a nonzero actual zero its residue is minus the weighted positive analytic multiplicity divided by the coordinate times its displacement from one, and its meromorphic order is exactly minus one.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/VerticalNearestPole.isolated_nearest_of_vertical_perturbation`
- Truth anchor: `D5/S3/Analytic/Isolation/VerticalNearestPole.real_center_spectral_dichotomy`
- Truth anchor: `D5/S3/Analytic/Isolation/VerticalNearestPole.regularized_positive_log_family`
- Dependency: [D5/S3/Analytic/Boundary/WeightedLogDerivativeResidue](../Boundary/WeightedLogDerivativeResidue.md)
