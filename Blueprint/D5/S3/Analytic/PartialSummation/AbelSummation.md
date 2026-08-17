# Finite Abel Summation

## Abstract

Finite Abel summation rewrites a weighted range sum using prefix sums.

**Theorem 1.1 (Finite Abel summation for a range sum).**

$$\sum_{i< n} f_{i} \cdot g_{i} = f_{n-1} \cdot \sum_{i< n} g_{i} - \sum_{i< n-1} {f_{i+1}-f_{i}} \cdot \sum_{j< i+1} g_{j}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PartialSummation/AbelSummation.abel_summation_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For scalar weights f and module-valued terms g, the weighted sum through n is the final weight times the full prefix sum, minus the sum of successive weight differences against shorter prefix sums.

The source also continues to analytic localization and asymptotic claims. This declaration formalizes only its finite algebraic Abel-summation step.

Pinned Mathlib supplies Finset.sum_range_by_parts. The Lean proof imports and applies that theorem directly.

## References

- Truth anchor: `D5/S3/Analytic/PartialSummation/AbelSummation.abel_summation_range`
