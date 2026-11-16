# Index equality patterns

## Abstract

Canonical equality-pattern decompositions of finite index sums

**Definition 1.1 (Four-index pattern sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.patternSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.patternSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum a function over injective representative tuples after composing with a prescribed map from four positions.

**Definition 1.2 (Three-index pattern sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.patternSum3`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.patternSum3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum a function over injective representative tuples after composing with a prescribed map from three positions.

**Theorem 1.3 (Three-index equality classification).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.sum_fin_three_eq_pattern_sums`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.sum_fin_three_eq_pattern_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every sum over triples decomposes into the five canonical patterns: three distinct indices, each of the three two-equal patterns, and one common index.

**Theorem 1.4 (Four-index equality classification).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.sum_fin_four_eq_pattern_sums`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.sum_fin_four_eq_pattern_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every sum over quadruples decomposes into the fifteen canonical equality patterns, grouped by multiplicities 1+1+1+1, 2+1+1, 2+2, 3+1, and 4.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.patternSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.patternSum3`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.sum_fin_four_eq_pattern_sums`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.sum_fin_three_eq_pattern_sums`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs](QuadraticMomentDefs.md)
