# The product of two quaternion comparison models

## Abstract

The product of the quaternion comparison model with itself is noncommutative, chain connected and touches zero, but its reading is not the Gram kernel of a map into Euclidean five-space.

**Theorem 1.1 (The product of two quaternion models does not have feature rank five).**

$$\operatorname{Noncommutative}\left(\operatorname{prod}\left(\operatorname{quaternionModel}, \operatorname{quaternionModel}\right)\right) \land \left(\operatorname{ChainConnected}\left(\operatorname{prod}\left(\operatorname{quaternionModel}, \operatorname{quaternionModel}\right)\right) \land \left(\operatorname{TouchesZero}\left(\operatorname{prod}\left(\operatorname{quaternionModel}, \operatorname{quaternionModel}\right)\right) \land \left(\neg \operatorname{HasFeatureRank}\left(\operatorname{prod}\left(\operatorname{quaternionModel}, \operatorname{quaternionModel}\right), 5\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionProductRank.prod_quaternionModel_not_hasFeatureRank_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product structure prod C D on pairs has the componentwise transfer and the product of the two readings. Since the quaternion model is noncommutative, chain connected and touches zero, the product with a second copy is noncommutative, chain connected and touches zero, by the corresponding statements for products. Suppose its reading had feature rank five. Then there is an injective map u from pairs of unit quaternions into the unit quaternions with u (tri x y z) = u x * (u y)^-1 * u z for all x, y, z. With o = (1, 1), the map w p = (u o)^-1 * u p satisfies w p * w p = (u o)^-1 * u (tri p o p), so every pair p with tri p o p = o and p different from o has w p * w p = 1 and w p different from 1. In the quaternions q * q = 1 forces q = 1 or q = -1, so w p = -1 for every such p. The two different pairs (-1, 1) and (1, -1) both satisfy tri p o p = o, since (-1) * 1^-1 * (-1) = 1. Hence they have the same image under w, and therefore under u, which contradicts injectivity.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionProductRank.prod_quaternionModel_not_hasFeatureRank_five`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](QuaternionComparisonModel.md)
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonProduct](TernaryComparisonProduct.md)
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonRankFive](TernaryComparisonRankFive.md)
