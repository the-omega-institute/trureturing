# Original finite words use the same unique ready extension

## Abstract

Original finite words use the same unique ready extension.

**Theorem 1.1 (Original finite words use the same unique ready extension).**

$$\forall a: \operatorname{List}\left(\operatorname{Fin}\left(11\right)\right), \operatorname{extendedPreparation}\left(a\right) = \operatorname{readyExtension}\left(\operatorname{originalPreparation}\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeReader/Original.original_preparation_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old source is every legal path b0 through b6 with fixed zero endpoints, of cardinality thirteen. sourceJ inserts b7=1,b8=0,b9=i,b10=0 and retains all old bits. Its code has 26 paths; all 63 complementary paths remain in Source. oldReady has b3=1 and is the literal old word 00100; its sourceJ image at i=false is readySource. Padding reinserts exactly the fixed exterior bits b(-1)=1 and b11=1, or b15=1 in the extended carrier. Every original projection is the existing weighted local path projection in these coordinates, including addresses zero and ten. The ready extension is the one source-defined tail, without column preparation, postselection, resampling or normalization. The matrix proof first derives that original addresses cannot leave this ready image, then identifies their entries with the original source coefficients. Every full forward pulse therefore intertwines, and induction proves the preparation identity for every finite eleven-address word from the unique original ready vector. The identity is an equality of complete vectors. It does not construct a Bell probability law or guarantee the current configuration has positive support; those remain required source obligations. Coordinate and algebra helpers earn no content; the live consumer is the source-specific no-jump statement at original preparation entrances.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeReader/Original.original_preparation_bridge`
- Dependency: [D5/S3/Quantum/Algebra/Knot/WeightedPathProjectionNaturality](../../Algebra/Knot/WeightedPathProjectionNaturality.md)
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Global](Global.md)
