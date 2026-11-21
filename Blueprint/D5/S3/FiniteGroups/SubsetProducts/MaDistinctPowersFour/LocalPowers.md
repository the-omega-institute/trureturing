# Power separation within generator classes of size two, three or four

## Abstract

Power separation within generator classes of size two, three or four.

**Theorem 1.1 (zpowers_pow_of_bound).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.zpowers_pow_of_bound`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.zpowers_pow_of_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

Every allowed exponent is coprime to the element order and preserves its cyclic subgroup.

**Theorem 1.2 (arrange_pair).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_pair`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

Both endpoint assignments failing would force the common element order to divide the difference of the squared exponents.

**Theorem 1.3 (arrange_triple).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_triple`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_triple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

The prime-divisor bounds make the three consecutive exponents distinct units modulo the full generator order. Their products with the three distinct generator coordinates form a Latin array over that unit group. The order-three transversal supplies a permutation whose selected products stay distinct modulo the full order. The generator coordinates transfer this permutation back to the original powers.

**Theorem 1.4 (arrange_four).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_four`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

Coordinates in the units modulo the common order transfer the modular four-block assignment to the original group.

## References

- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_four`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_pair`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_triple`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.zpowers_pow_of_bound`
- Dependency: [D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/ModularBlock](ModularBlock.md)
- Dependency: [D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderThree](OrderThree.md)
- Dependency: [D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/SourceClaim](SourceClaim.md)
