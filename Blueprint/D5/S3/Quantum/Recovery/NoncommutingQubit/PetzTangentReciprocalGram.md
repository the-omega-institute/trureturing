# Paired reciprocal Gram bounds for the Petz tangent

## Abstract

The two parity sectors of the qubit tangent residual obey the common marginal-dependent reciprocal Gram bound.

**Theorem 1.1 (Combined reciprocal parity estimate).**

Lean statement: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<g≤1, 0<δ≤1, and real β with g²+β²=1, the squared modulus of g(a+b)+β(c+d) is bounded by 1+2/(1+δ²) times the sum of the two weighted reciprocal energies. For the arcsine functionals, the even coefficients are normalized by 1/x and the odd coefficients by 1/(x(x+g)), for nodes x in {1,δ}. The estimate allows arbitrary complex coefficients and the maximally mixed marginal δ=1.

The odd Gram splits into a common even lower Gram and a positive correction with unsquared reciprocal nodes. The even estimate uses the square-root chord bound. Both sector estimates apply to the real and imaginary parts of the coefficients and retain the two-node cross terms.

The physical common-reference tangent application requires the arcsine evaluations and substitution back to the affine spectral variable, followed by identification with the actual arithmetic BKM residual and ordinary Petz sandwich.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](../../Divergence/UmegakiRareFlagBKM.md)
