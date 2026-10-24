# Second minors

## Abstract

Positive semidefinite kernels of second minors.

**Theorem 1.1 (Positivity for arbitrary index pairs).**

Lean statement: `D5/S3/Analytic/MomentMinors/PairMinor.pairMinor_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MomentMinors/PairMinor.pairMinor_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite real positive semidefinite matrix A and any finite family of ordered pairs (p(a),q(a)), the matrix with entries A(p(a),p(b)) A(q(a),q(b)) - A(p(a),q(b)) A(q(a),p(b)) is positive semidefinite. Pairs may repeat, coincide, or overlap.

In the tensor square, send each pair to the difference of its two ordered coordinate vectors. Congruence of A tensor A by this map gives twice the displayed matrix. Positivity follows from positivity of the Kronecker product, congruence, and multiplication by the nonnegative scalar one half.

## References

- Truth anchor: `D5/S3/Analytic/MomentMinors/PairMinor.pairMinor_posSemidef`
