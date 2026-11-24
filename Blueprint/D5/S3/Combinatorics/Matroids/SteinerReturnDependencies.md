# Compatibility of Steiner Circuit Returns

## Abstract

A linear condition for simultaneous returns in a central extension of a Steiner loop.

**Theorem 1.1 (Realizing compatible circuit returns).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerReturnDependencies.realizesExactlyCompatibleReturns`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerReturnDependencies.realizesExactlyCompatibleReturns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Fix a Steiner loop with trivial centre, an additive group of exponent at most two, and a family of requests. Each request names a pair of matching pivots, an alternating component via one representative, and a desired shift in the fibre. At a periodic representative the first quotient return occurs after the minimal period of the two-step map. All representatives are periodic in a finite loop. At an aperiodic representative the minimal period convention gives zero rounds and a zero row, so the only compatible shift is zero.

The row of a request counts each triple in those rounds modulo two. Steps involving the identity or a repeated point have zero label and contribute nothing. One assignment of labels realizes all requests exactly when every finitely supported binary combination of zero total row also has zero total desired shift.

Evaluating the row at the triple labels gives the shift by iterating the extension multiplication. This proves necessity. For sufficiency, the relation condition defines a linear map on the span of the rows. Extend the map to the entire free vector space and read the labels on its basis. The resulting loop has centre equal to the identity fibre. Reversing the circuit along a matching step negates the shift, which preserves its value in a group of exponent at most two, so all starts in the requested component have the prescribed return.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerReturnDependencies.realizesExactlyCompatibleReturns`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerSchreierExtension](SteinerSchreierExtension.md)
