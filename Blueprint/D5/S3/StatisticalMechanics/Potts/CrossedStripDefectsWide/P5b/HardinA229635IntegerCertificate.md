# Signed residual certificate

## Abstract

The checked initial vector and sparse steps imply a zero scalar residual at every offset.

**Theorem 1.1 (Forward iteration from a table).**

$$\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(M, v, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right) = p\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.forward_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Let M be a square integer matrix on Fin d, v an integer row vector, and i an index of Fin 31. Let p assign a row vector to each index of Fin 31. Assume next maps each row vector w to Matrix.vecMul(w,M), p at zero equals v, and p at the successor of each j in Fin 30 equals next applied to p at j cast to Fin 31. Then the displayed equality gives the forward iterate at i.

**Theorem 1.2 (Vanishing scalar residual at every offset).**

$$\forall t: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{residual}}\left(\operatorname{T}, \operatorname{\mathit{initial}}, \operatorname{\mathit{terminal}}, t\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_all_offsets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The initial row vector and all thirty transitions fix the powers needed by the signed lag vector. Four disjoint coordinate ranges cover that vector. Its terminal readout vanishes at offset zero. Its image under one matrix step is zero, so every positive offset has zero readout.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.forward_table`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_all_offsets`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck0](HardinA229635PowerCheck0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck1](HardinA229635PowerCheck1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck2](HardinA229635PowerCheck2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual](HardinA229635Residual.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Sparse](HardinA229635Sparse.md)
