# Simultaneous Returns over a Boolean Steiner Subloop

## Abstract

Three alternating squares on the same four vertices constrain their simultaneous returns.

**Theorem 1.1 (The exact simultaneous return range for three pivots).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.simultaneousReturns`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.simultaneousReturns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Embed the eight binary vectors with exclusive-or as a multiplicatively closed subset. Use the three nonidentity pivots in a subgroup of order four. On the complementary four vertices each pair of pivot matchings forms a square.

Each square return sums the labels along two matching colours. Every edge label occurs in two of the three returns. In an abelian group where doubling is zero, the three returns therefore sum to zero. Conversely, set the label of one edge of the second colour and one edge of the third colour to the first two requested returns. The remaining labels can be zero. This realizes all compatible triples at every corner and for every starting fibre coordinate.

**Theorem 1.2 (A centreless quotient with an incompatible prescription).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.existsCentrelessObstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.existsCentrelessObstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Take three copies of the order-ten Steiner loop of the affine plane over the field with three elements. The centre of the product is trivial. Selecting the identity and one nonidentity point in each factor embeds the required Boolean subloop.

With the two-element additive fibre, a return of one for only the first square and zero for the other two violates the parity equation. The obstruction occurs in a centreless Steiner loop of order one thousand.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.existsCentrelessObstruction`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.simultaneousReturns`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerSchreierExtension](SteinerSchreierExtension.md)
