# Actual ordinary-sector collision transport

## Abstract

LatticeSectorChannelTransport

**Theorem 1.1 (iterate_borcherds).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.iterate_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.iterate_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original all-integer canonical Borcherds identity, with the first state truncated on the original third state, gives the cleared iterate as a finite-support signed binomial residue.

For arbitrary integral symmetric even lattice data, charges and descendant states, the actual state-field locality and statewise truncation bounds give a common vector power series P. The clearing exponent N is independent of the third state. The product and reverse product have cleared coefficients P; original Borcherds with p=A identifies the cleared iterate with P(t+y,y), retaining signed integer binomial coefficients. Supported finite inverse expansions recover the ordered product and iterate in their respective chambers. The canonical field keeps its original lattice cocycle. FullIO transport uses the two existing fullUniversal equivalences and charge reassociation, and is consumed by the supported equation for every lawful finite-target field, including repeated target charges. Only this classification consumer requires a two-sided complex Gram inverse. No sewing law, positivity, homogeneity or finite descendant cutoff is assumed. These coefficient theorems make no braided-category, pentagon, Monster, anomaly, CFT, string-theory or AdS/CFT realization claim.

**Definition 1.2 (product).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.product`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope.

**Definition 1.3 (reverseProduct).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.reverseProduct`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.reverseProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope.

**Definition 1.4 (iterate).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.iterate`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.iterate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope.

**Definition 1.5 (clearIterate).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.clearIterate`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.clearIterate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope.

**Theorem 1.6 (ordinary_actual_cleared_channel_transport).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.ordinary_actual_cleared_channel_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.ordinary_actual_cleared_channel_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope.

**Definition 1.7 (fullChannel).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.fullChannel`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.fullChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope.

**Theorem 1.8 (fullIO_supported_channel_transport).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.fullIO_supported_channel_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.fullIO_supported_channel_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.clearIterate`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.fullChannel`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.fullIO_supported_channel_transport`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.iterate`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.iterate_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.ordinary_actual_cleared_channel_transport`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.product`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.reverseProduct`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries](../FormalSeries/SupportedChannelSeries.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorFullFusion](LatticeSectorFullFusion.md)
