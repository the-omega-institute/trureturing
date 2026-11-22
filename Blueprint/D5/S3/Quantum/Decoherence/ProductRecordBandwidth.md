# Binary product records and Gibbs bath bandwidth

## Abstract

Sharp bandwidth for binary product records and separation from bounded cq conditional entropy.

**Theorem 1.1 (The required width is a sum over overlaps).**

Lean statement: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_requiredWidth`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_requiredWidth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For overlaps 0 ≤ s_j < 1 the product memory has binary factors (1 ± s_j)/2 in its eigenbasis. The required width is β⁻¹ times the sum of log((1+s_j)/(1−s_j)).

**Theorem 1.2 (Product lower bounds on bandwidth and dimension).**

Lean statement: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_bandwidth_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_bandwidth_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb, Michael J. Kastoryano and Michael M. Wolf (2011). *Hilbert’s projective metric in quantum information theory*. DOI: [10.1063/1.3615729](https://doi.org/10.1063/1.3615729). URL: <https://arxiv.org/abs/1102.5170v2>.

*Commentary.*

For any finite reduced preparation using an independent Gibbs bath, the spectral width is bounded below by the exact product formula, and the bath dimension is at least the product of (1+s_j).

**Theorem 1.3 (A product-sized bath attains the product width).**

Lean statement: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_bandwidth_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_bandwidth_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

Indexing the bath by binary words gives the aligned Gibbs bath and an attaining tensor swap for the reduced preparation.

**Theorem 1.4 (The product spectrum is an actual pure-record marginal).**

Lean statement: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.productCQ_memory`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.productCQ_memory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform classical–quantum ensemble uses explicit normalized pure tensor records with the given local overlaps. Its average record is diagonal and has precisely the product spectrum.

**Theorem 1.5 (Conditional entropy of the explicit cq state).**

Lean statement: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.productCQ_conditionalEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.productCQ_conditionalEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lidia del Rio, Johan Åberg, Renato Renner, Oscar Dahlsten and Vlatko Vedral (2011). *The thermodynamic meaning of negative entropy*. DOI: [10.1038/nature10123](https://doi.org/10.1038/nature10123). URL: <https://arxiv.org/abs/1009.1630v2>.

*Commentary.*

The von Neumann entropy of the joint state minus that of its record marginal equals the sum of log 2 minus the binary entropy at (1+s_j)/2. Entropy is measured in nats.

**Theorem 1.6 (Asymptotic dimensionless width).**

Lean statement: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_width_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_width_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an envelope for the row overlaps tends to zero and the row sum of squares tends to λ > 0, the dimensionless width divided by twice the sum of overlaps tends to one.

**Theorem 1.7 (Bounded cq conditional entropy with divergent bandwidth).**

Lean statement: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.productCQ_small_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.productCQ_small_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lidia del Rio, Johan Åberg, Renato Renner, Oscar Dahlsten and Vlatko Vedral (2011). *The thermodynamic meaning of negative entropy*. DOI: [10.1038/nature10123](https://doi.org/10.1038/nature10123). URL: <https://arxiv.org/abs/1009.1630v2>.

*Commentary.*

With the same triangular-array assumptions and fixed β > 0, the exact required bandwidth tends to infinity, while the actual cq conditional entropy eventually lies in [0, λ+1]. The exact optimization is stated for the preparation of the product memory from the maximally mixed state.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.productCQ_conditionalEntropy`
- Truth anchor: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.productCQ_memory`
- Truth anchor: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.productCQ_small_overlap`
- Truth anchor: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_bandwidth_attained`
- Truth anchor: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_bandwidth_lower_bound`
- Truth anchor: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_requiredWidth`
- Truth anchor: `D5/S3/Quantum/Decoherence/ProductRecordBandwidth.product_width_asymptotic`
- Dependency: [D5/S3/Entropy/EntropyEquality](../../Entropy/EntropyEquality.md)
- Dependency: [D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy](../../Entropy/NamingWindow/GreenClassWindowEntropy.md)
- Dependency: [D5/S3/Quantum/Decoherence/GibbsBathBandwidth](GibbsBathBandwidth.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Information/StrongSubadditivity](../Information/StrongSubadditivity.md)
