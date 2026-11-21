# Incoming lists for states 32 through 63

## Abstract

The stored incoming list agrees with a scan of every outgoing list, with duplicates preserved.

**Theorem 1.1 (Incoming lists for states 32 through 63).**

$$\forall j: \operatorname{\mathit{Fin}}\left(32\right), (\operatorname{\mathit{let}} k: \operatorname{\mathit{State}} := 32 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right); (\operatorname{\mathit{incomingClasses}}\left(k\right) = \operatorname{\mathit{transposeLists}}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseCheck1.exact_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The stored incoming list agrees with a scan of every outgoing list, with duplicates preserved.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseCheck1.exact_transpose`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData](HardinA229635SparseData.md)
