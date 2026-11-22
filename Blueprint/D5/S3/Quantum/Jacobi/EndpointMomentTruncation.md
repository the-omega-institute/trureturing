# Endpoint moments of a finite Jacobi section

## Abstract

For a Jacobi chain cut at site n, the first possible error in its endpoint moments occurs at order 2n and equals the product of squared couplings up to the cut.

**Definition 1.1 (Powers applied to the endpoint vector).**

Lean statement: `D5/S3/Quantum/Jacobi/EndpointMomentTruncation.amplitude`

*Formalization.* `D5/S3/Quantum/Jacobi/EndpointMomentTruncation.amplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial vector is the unit mass at site zero. Each time step applies the tridiagonal recurrence with real diagonal entries and real symmetric nearest-neighbor couplings. With a cutoff n, every site starting at n is set to zero initially and after each step.

**Theorem 1.2 (The first possible endpoint moment error).**

$$m_{2n} - \left(m_{2n}\right)^{(n)} = \prod_{j<n}\left(b_{j}\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Jacobi/EndpointMomentTruncation.first_omitted_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full endpoint moment at degree k equals the moment of the first n sites whenever k is below 2n. At degree 2n their difference is the product of the squares of the first n couplings. For the empty section the difference at degree zero is one.

Reaching the first omitted site takes at least n steps, and returning to the endpoint takes n more. The outward and inward paths of minimal length both traverse each of the first n edges exactly once. For n at least one, if the product of the squares of the preceding n−1 couplings is known and nonzero, division by that product and taking the nonnegative square root gives the magnitude of the final coupling. A zero earlier coupling makes this readout vanish.

## References

- Truth anchor: `D5/S3/Quantum/Jacobi/EndpointMomentTruncation.amplitude`
- Truth anchor: `D5/S3/Quantum/Jacobi/EndpointMomentTruncation.first_omitted_moment`
