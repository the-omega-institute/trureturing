# Complete Exceptional Tensor Sector

## Abstract

Native tensor coordinates characterize every finite superposition in the zero-charge zero-energy sector.

**Theorem 1.1 (Original total zero mode and fixed charge).**

$$\forall D, H, v, H\times \operatorname{gramComplex}\left(D\right) = 1 \land \operatorname{gramComplex}\left(D\right)\times H = 1 \Rightarrow v \in \operatorname{sector}\left(D\right) \iff \operatorname{chargeSupportZero}\left(v\right) \land \operatorname{TotalZeroMode}\left(v\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeEnergyBasis.mem_sector_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full matter basis is indexed by every integral charge and every finite oscillator exponent. Tensoring it with the complete exterior ghost basis gives coordinates for the unrestricted actual carrier. Both inverse-Gram equations identify the original matter zero mode with oscillator frequency plus half the lattice norm; the original ghost zero stress is diagonal with the native signed site energy.

Membership is equivalent to having no nonzero-charge coefficient and being killed by the original total zero mode. This equivalence holds for every finite superposition, not just for isolated tensor monomials. No null direction, adapted partner, frame, division by a charge pairing, or signature condition occurs.

**Theorem 1.2 (Finite basis and exact dimension).**

$$\forall D, \operatorname{finrank}\left(Complex, \operatorname{sector}\left(D\right)\right) = 4 + 2\times \operatorname{rank}\left(D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeEnergyBasis.sector_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Four ground tensors have ghost subsets empty, {3}, {1,5}, and {1,3,5}. For each matter axis there are two additional tensors: its frequency-one excitation with ghost subset {1}, or with ghost subset {1,3}. The label equivalence is injective and surjective onto the entire proved energy fiber, and its inverse transports the full coefficient equivalence to an explicit basis.

The original integer ghost-number operator has respective eigenvalues 0, 1, 2, and 3 on the four ground tensors, and 1 and 2 on the two tensors for each matter axis. This is a chain-space calculation; its dimension is not a cohomology dimension.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeEnergyBasis.mem_sector_iff`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeEnergyBasis.sector_finrank`
- Dependency: [D5/S3/VertexAlgebra/OriginalZeroChargeEnergySector](OriginalZeroChargeEnergySector.md)
