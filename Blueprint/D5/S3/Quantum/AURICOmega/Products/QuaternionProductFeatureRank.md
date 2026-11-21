# Feature dimension of a product of quaternion readings

## Abstract

The full Cartesian product of n unit-quaternion readings has least real feature dimension five to the n.

**Definition 1.1 (Reading of two ordered tuples).**

Lean statement: `D5/S3/Quantum/AURICOmega/Products/QuaternionProductFeatureRank.productReading`

*Formalization.* `D5/S3/Quantum/AURICOmega/Products/QuaternionProductFeatureRank.productReading` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the n readings in the corresponding positions of the two tuples.

**Theorem 1.2 (Least real feature dimension on the full Cartesian product).**

$$\forall n \in \mathbb{N},\ \operatorname{leastFeatureDimension}(K_{n}) = 5^{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/Products/QuaternionProductFeatureRank.least_feature_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit quaternions q and p, the single-factor reading is (1 + inner(q,p))/2. Given any natural number n, compare two ordered n-tuples by multiplying their corresponding factor readings. The least dimension of a real Euclidean space in which all such comparisons are inner products of feature vectors equals 5^n. The empty tuple has reading one and requires one feature coordinate.

For one quaternion the normalized feature vector is (1,q)/sqrt(2). Taking all coordinate products gives a Euclidean map with 5^n coordinates. For the opposite bound, sample 1, -1, i, j and k in each coordinate. The single-factor Gram determinant is 1/8. The Gram matrix of the Cartesian grid is its n-fold Kronecker power, which is invertible. Any map realizing the reading must therefore send all 5^n grid points to linearly independent vectors. The lower bound uses the full grid.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/Products/QuaternionProductFeatureRank.least_feature_rank`
- Truth anchor: `D5/S3/Quantum/AURICOmega/Products/QuaternionProductFeatureRank.productReading`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](../QuaternionComparisonModel.md)
