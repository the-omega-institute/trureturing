# A quantitative stability envelope for broken pairing symmetry

## Abstract

Quantitative Cauchy stability for the six-independent-length determinant remainder.

For the six-independent-length character coordinates, let t be the squared Euclidean size of the two asymmetry coordinates. Let C be the center coefficient obtained by adding ro-1 to the Euclidean norm of (A squared minus B squared, r minus o).

**Theorem 1.1 (The asymmetry remainder has a quadratic-plus-quartic envelope).**

$$\forall r \in Real, o \in Real, A \in Real, B \in Real, xi \in Real, zeta \in Real,\; Xi\left(r, o, A, B, xi, zeta\right) \le asymmetrySize\left(xi, zeta\right)^{2} + 2 \cdot stabilityCoefficient\left(r, o, A, B\right) \cdot asymmetrySize\left(xi, zeta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.asymmetry_remainder_le_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic part of Xi is bounded by 2 C t through the two-dimensional Cauchy inequality, while the quartic part is at most t squared. This is the new estimate that controls both independent symmetry-breaking directions.

**Theorem 1.2 (The stability envelope forces a negative determinant).**

$$\forall r \in Real, o \in Real, A \in Real, B \in Real, xi \in Real, zeta \in Real,\; asymmetrySize\left(xi, zeta\right)^{2} + 2 \cdot stabilityCoefficient\left(r, o, A, B\right) \cdot asymmetrySize\left(xi, zeta\right) < L\left(r, o, A, B\right) \cdot M\left(r, o, A, B\right) \Rightarrow det\left(gram\left(r, o, A, B, xi, zeta\right)\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.determinant_negative_of_stability_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Whenever the envelope t squared plus 2 C t is strictly below the product L M, the exact determinant remainder identity gives a negative Gram determinant. The implication only uses that strict bound; positive-length and geometric realization conditions remain separate hypotheses of the surrounding model.

**Theorem 1.3 (The strict envelope is equivalent to a square-root radius).**

$$\forall r \in Real, o \in Real, A \in Real, B \in Real, xi \in Real, zeta \in Real,\; 0 < L\left(r, o, A, B\right) \Rightarrow \left(0 < M\left(r, o, A, B\right) \Rightarrow \left(0 < stabilityCoefficient\left(r, o, A, B\right) \Rightarrow \left(asymmetrySize\left(xi, zeta\right) < stabilityRadius\left(r, o, A, B\right) \Leftrightarrow asymmetrySize\left(xi, zeta\right)^{2} + 2 \cdot stabilityCoefficient\left(r, o, A, B\right) \cdot asymmetrySize\left(xi, zeta\right) < L\left(r, o, A, B\right) \cdot M\left(r, o, A, B\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.stability_bound_iff_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When L and M are positive and C is positive, the strict quadratic-plus-quartic bound is equivalent to t being below sqrt(C squared plus L M) minus C. This is a sufficient radius for the six-length determinant criterion, not a claim that the radius is a maximal geometric ball.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.asymmetry_remainder_le_envelope`
- Truth anchor: `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.determinant_negative_of_stability_bound`
- Truth anchor: `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.stability_bound_iff_radius`
- Dependency: [D5/S3/Geometry/Hyperideal/SixIndependentLengthRemainder](SixIndependentLengthRemainder.md)
