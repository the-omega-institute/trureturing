# Sparse update correctness

## Abstract

The incoming lists implement multiplication by the exact transfer matrix.

**Theorem 1.1 (Correctness of the sparse update).**

$$\forall v: (\operatorname{\mathit{State}}) \to (\operatorname{\mathit{Int}}), (\operatorname{\mathit{step}}\left(v\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(v, \operatorname{T}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Sparse.step_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The update sums the source weights from the checked incoming list. Counting occurrences gives each matrix entry, including multiplicities in the inherited block.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Sparse.step_correct`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseCheck0](HardinA229635SparseCheck0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseCheck1](HardinA229635SparseCheck1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseCheck2](HardinA229635SparseCheck2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseCheck3](HardinA229635SparseCheck3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer](HardinA229635Transfer.md)
