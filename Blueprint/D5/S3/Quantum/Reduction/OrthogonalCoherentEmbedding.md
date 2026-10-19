# OrthogonalCoherentEmbedding

## Abstract

Orthogonal component coding with complete CPTP padding attains the exact minimum coherent port dimension.

The component quotient retains the arbitrary original probe family. Its finiteness follows from orthonormal representatives in finite dimension. An orthonormal basis of each actual component supplies a coordinate frame. Zero padding embeds these coordinates into a common coherent block whose dimension is the largest component dimension. The encoder stores the component as a classical flag; the decoder applies the frame inverse on the encoded support and prepares a fixed unit probe on the unused complement. Thus the decoder is completely positive and trace preserving on the entire coherent block. The composite pinches between orthogonal components, and every original probe belongs to one component, so its probability is preserved for all density inputs. Conversely every actual encoder-decoder Kraus matrix factors through the coherent block; the scalarity theorem and normalization force one nonzero scalar on each component, yielding the matching rank bound. This is the measurement-relative compression structure described by Bluhm, Rauber, and Wolf, with the nondisturbance rigidity of Mayer and Knill.

**Theorem 1.1 (components finite).**

Lean statement: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.components_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.components_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The quotient of any family of unit probes by the nonorthogonality component relation is finite.

**Theorem 1.2 (components orthogonal).**

Lean statement: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.components_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.components_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The actual Hilbert spans of distinct components are orthogonal.

**Theorem 1.3 (components span).**

Lean statement: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.components_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.components_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

When the original arbitrary probe family has full complex span, the supremum of its component Hilbert subspaces is the full space.

**Theorem 1.4 (probe channel block form).**

Lean statement: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.probe_channel_block_form`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.probe_channel_block_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

Universal probe probability preservation gives normalized environment coefficients on the proved-finite graph components. Every Kraus matrix is their scalar-weighted projection sum. The channel action on every matrix is the double component sum weighted by the overlaps of those environment vectors.

**Theorem 1.5 (orthogonal decomposition port).**

Lean statement: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.orthogonal_decomposition_port`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.orthogonal_decomposition_port` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

Every finite orthogonal spanning decomposition with unit vectors in its components admits an actual finite flagged port at any coherent dimension bounding the component dimensions. The encoder and every decoder Kraus matrix are identified explicitly by the orthonormal frame, zero padding, and the complement-filled decoder family. The fixed unit vector lies in its component, and the fixed density is proved to satisfy P times the density times P equals that density.

**Theorem 1.6 (exact component port dimension).**

Lean statement: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.exact_component_port_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.exact_component_port_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

For any arbitrary unit probe family with full complex span in a finite Hilbert space, the minimum coherent port dimension equals the maximum dimension of its nonorthogonality components. The lower bound covers arbitrary finite flags whose probabilities may depend on the input. The constructed port has the proved-finite component quotient as flags and preserves every original probe probability on every density input. At this dimension, every component embedding has adjoint Gram matrix equal to its actual component projection, the port decoder Kraus matrices are the explicit complement-filled family, and the prepared probe density is proved to be supported in that component. Its composite is exactly orthogonal component pinching. The same theorem also supplies actual canonical completely positive trace-preserving encoder and decoder maps on the flagged algebra, whose all-matrix composition equals that pinching map and whose encoder is proved to have classical diagonal flag outputs.

For a finite coordinate type V, arbitrary original edge labels E, and endpoint maps u and v, FiniteEdgeProbeCorrespondence.construction supplies the unit and spanning hypotheses for its loop-corrected vertex-and-edge menu. Apply exact_component_port_dimension to that menu: its actual component spaces are the coordinate spaces of the endpoint-generated graph classes, and their dimensions are exactly the numbers of vertices in those classes. Thus the existing coherent-port minimum is the largest component vertex count, independently of repeated labels, orientation, loops, or isolated vertices. For actual FIB choices at t at least two, use ActiveVertex(c) and every label in Fin(3t-3), lift the endpoints of chosenPair, and apply restricted_endpoint_closure. Product extensionality identifies the ambient endpoint generators with SupportArrow(c), deriving the activeSetoid(c) correspondence. Finiteness and nonemptiness of the active domain follow from the nonzero modulus and an endpoint of label zero; Balanced is unnecessary. The channel block theorem applies with its trace-preserving Kraus identity and probability preservation for every density input and every original probe. Its cross-component environment Gram coefficients remain in the formula. The native state, observer, preparation and instrument interpretation is an additional unsupplied bridge.

## References

- Truth anchor: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.components_finite`
- Truth anchor: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.components_orthogonal`
- Truth anchor: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.components_span`
- Truth anchor: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.exact_component_port_dimension`
- Truth anchor: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.orthogonal_decomposition_port`
- Truth anchor: `D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.probe_channel_block_form`
- Dependency: [D5/S3/Quantum/Reduction/CoherentFlagPort](CoherentFlagPort.md)
- Dependency: [D5/S3/Quantum/Reduction/ProbeComponentRigidity](ProbeComponentRigidity.md)
