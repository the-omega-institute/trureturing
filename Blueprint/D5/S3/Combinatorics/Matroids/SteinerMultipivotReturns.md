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

**Theorem 1.2 (A Boolean subloop in a centreless product).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.existsCentrelessBooleanCube`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.existsCentrelessBooleanCube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Take three copies of any centreless Steiner loop with a nonidentity point. That point and the identity form a two-element subloop. Their product embeds the eight binary vectors, and the centre of the ambient product is the identity alone.

Applying the simultaneous return criterion to this embedding with a two-element fibre rules out prescribing a return of one for just one of the squares.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.existsCentrelessBooleanCube`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns.simultaneousReturns`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerSchreierExtension](SteinerSchreierExtension.md)
