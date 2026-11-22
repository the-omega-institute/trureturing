# Signed residual certificate

## Abstract

The checked initial vector and sparse steps imply a zero scalar residual at every offset.

**Theorem 1.1 (Vanishing scalar residual at every offset).**

$$\forall t: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{residual}}\left(\operatorname{T}, \operatorname{\mathit{initial}}, \operatorname{\mathit{terminal}}, t\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_all_offsets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The initial row vector and all thirty transitions fix the powers needed by the signed lag vector. Four disjoint coordinate ranges cover that vector. Its terminal readout vanishes at offset zero. Its image under one matrix step is zero, so every positive offset has zero readout.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_all_offsets`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck0](HardinA229635PowerCheck0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck1](HardinA229635PowerCheck1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck2](HardinA229635PowerCheck2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual](HardinA229635Residual.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Sparse](HardinA229635Sparse.md)
