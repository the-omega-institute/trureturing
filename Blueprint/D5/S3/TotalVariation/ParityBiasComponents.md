# Connected components of a fixed-law bias fiber

## Abstract

At fixed columns and raw offset, the connected components of the bias fiber are contractible.

**Theorem 1.1 (A fixed sign region is contractible).**

Lean statement: `D5/S3/TotalVariation/ParityBiasComponents.signSector_contractible`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityBiasComponents.signSector_contractible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an input column at each label in a finite binary vector space, a raw affine offset, and a reference bias family. Consider all signed biases of absolute value at most one producing the reference law at those columns and offset. At any point of this fiber, prescribe its sign on every label whose column projects nontrivially modulo the fair subgroup. The resulting subtype is contractible. The contraction scales the fair-subgroup coordinates to zero and interpolates logarithmic absolute biases on the other coordinates while keeping their signs fixed.

**Theorem 1.2 (The nonzero quotient columns distinguish the connected components).**

Lean statement: `D5/S3/TotalVariation/ParityBiasComponents.connectedComponent_eq_signSector`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityBiasComponents.connectedComponent_eq_signSector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the subspace topology on the fiber, a bias vector belongs to the connected component of a given realization exactly when the two vectors have the same signs on all labels outside the fair subgroup. The biases at those labels cannot vanish in the fiber. The sign regions are open, closed, and connected.

**Theorem 1.3 (The binary sign equation counts the components).**

Lean statement: `D5/S3/TotalVariation/ParityBiasComponents.card_biasFiber_components`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityBiasComponents.card_biasFiber_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the reference biases have absolute value at most one, let J be the labels with nonzero quotient columns and let r be the dimension of their span. The number of distinct connected components is two to the power of the size of J minus r. The feasible sign vectors are a fiber of the binary linear map sending a coefficient vector to its sum of projected columns. Changing the signs of the reference magnitudes realizes every coefficient vector in this fiber.

## References

- Truth anchor: `D5/S3/TotalVariation/ParityBiasComponents.card_biasFiber_components`
- Truth anchor: `D5/S3/TotalVariation/ParityBiasComponents.connectedComponent_eq_signSector`
- Truth anchor: `D5/S3/TotalVariation/ParityBiasComponents.signSector_contractible`
- Dependency: [D5/S3/TotalVariation/MinimumParityRealizations](MinimumParityRealizations.md)
