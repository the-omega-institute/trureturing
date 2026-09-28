# Finite Sector Channel Model

## Abstract

The exact objects and quantified claims for finite sector channel optimality.

These definitions support the physical construction, upper and lower estimates, and flat feasibility proofs. They carry no standalone optimality assertion.

**Definition 1.1 (Finite sector spectral data).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.Model`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.Model` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Model fixes a finite sector type, positive target rank in every sector, and a common finite list of nonnegative, decreasing spectral values whose sum is one in each sector.

**Definition 1.2 (Residual Gram kernel).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.kernel`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel pairs two sectors by summing products of square roots of their residual spectral values at the same coordinate.

**Definition 1.3 (Spectral minimum).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.spectralMinimum`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.spectralMinimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum is over every probability weight on the finite sector type of its quadratic form in the residual Gram kernel.

**Definition 1.4 (Actual encoding channels).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.EncodingChannels`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.EncodingChannels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source and target are quantum channels whose complete matrix actions are prescribed by the respective isometric encoding matrices.

**Definition 1.5 (Tensor matrix action).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.tensorRawAction`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.tensorRawAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The action expands arbitrary local channels against every physical input matrix unit, retaining both input and output indices.

**Definition 1.6 (Product realization).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.TensorRealization`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.TensorRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A joint channel realizes the product of two local channels when its matrix action equals tensorRawAction for every physical input matrix.

**Definition 1.7 (Mixture realization).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.MixtureRealization`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.MixtureRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A joint channel realizes a finite shared-classical mixture when its action on every input matrix equals the weighted sum of product actions.

**Definition 1.8 (Product error set).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.productErrors`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.productErrors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every member is the unhalved diamond distance of an actual joint product channel after the source encoding from the target encoding.

**Definition 1.9 (Mixture error set).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.mixtureErrors`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.mixtureErrors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every member is the corresponding distance of a finite probability mixture of actual product channels.

**Definition 1.10 (Full optimality claim).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.FullOptimalityClaim`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.FullOptimalityClaim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim includes actual encodings, every product and mixture realization, both unrestricted infima and product attainment.

**Definition 1.11 (Constructive optimality claim).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.ConstructiveOptimalityClaim`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.ConstructiveOptimalityClaim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same splitter has exact all-matrix partial-trace and Schur actions, exact basis outputs, diamond equality, and both attained infima.

**Definition 1.12 (Flat feasibility claim).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.FlatFeasibilityClaim`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.FlatFeasibilityClaim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary positive source and target ranks, exact basis output by local channels is equivalent to every source rank being a positive integer multiple of its target rank.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.ConstructiveOptimalityClaim`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.EncodingChannels`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.FlatFeasibilityClaim`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.FullOptimalityClaim`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.MixtureRealization`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.Model`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.TensorRealization`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.kernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.mixtureErrors`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.productErrors`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.spectralMinimum`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.tensorRawAction`
- Dependency: [D5/S3/Quantum/Entanglement/SectorSchmidtEncoding](SectorSchmidtEncoding.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
