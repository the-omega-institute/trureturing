# Exact Residue-Code Minimum Distance

## Abstract

The minimum Hamming distance of a bounded residue code is determined exactly by the largest product-bounded coordinate subset.

**Theorem 1.1 (Exact residue-code minimum distance).**

$$\begin{gathered}\forall m: \mathbb{N} \to \mathbb{N}, n, K \in \mathbb{N},\\{}((\forall i, i < n \Rightarrow 2 \leq \operatorname{m}(i)) \land\\{}(\forall i, j, i < j \land j < n \Rightarrow \operatorname{m}(i) < \operatorname{m}(j)) \land\\{}(\forall i, j, i < n \land j < n \land i \neq j \Rightarrow \gcd(\operatorname{m}(i), \operatorname{m}(j)) = 1) \land\\{}2 \leq K \leq \prod_{i < n} \operatorname{m}(i)) \Rightarrow\\{}\operatorname{residueMinimumDistance}(m, n, K) = n - \operatorname{maximumBlindCoordinateCount}(m, n, K).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ExactResidueCodeMinimumDistance.exact_residue_code_minimum_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minimum-distance object is the infimum of the Hamming distances between distinct messages in the bounded range. The blind-coordinate object is independently the maximum cardinality of a coordinate subset whose modulus product is below that range.

Sorting makes the first r moduli the least product among all r-coordinate subsets. The maximal blind count therefore lies between two adjacent prefix thresholds, and the frozen dynamic-range characterization turns those thresholds into the exact distance equality.

## References

- Truth anchor: `D5/S3/Arith/Coding/ExactResidueCodeMinimumDistance.exact_residue_code_minimum_distance`
- Dependency: [D5/S3/Arith/Coding/ResidueCodeDynamicRange](ResidueCodeDynamicRange.md)
