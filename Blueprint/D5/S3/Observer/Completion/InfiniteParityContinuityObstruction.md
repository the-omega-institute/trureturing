# Infinite Parity Continuity Obstruction

## Abstract

Total parity on finite-support Boolean configurations has no continuous completion on the full countable product.

**Theorem 1.1 (Finite-support total parity has no continuous completion).**

$$\neg \left(\exists extension \in \left(\mathbb{N} \to Bool\right) \to Bool,\; \operatorname{Continuous}\left(extension\right) \land \left(\forall support \in \operatorname{Finset}\left(\mathbb{N}\right),\; extension\left(\operatorname{readout}\left(support\right)\right) = \operatorname{decide}\left(\operatorname{Odd}\left(\operatorname{card}\left(support\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/InfiniteParityContinuityObstruction.finite_support_parity_has_no_continuous_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite set of natural-number coordinates represents a finite prime configuration through the canonical readout map. Its total parity is the Boolean decision of odd support cardinality.

The initial-segment configurations converge coordinatewise to the all-active path. Continuity into the discrete Boolean space would make their parity eventually constant, while consecutive even and odd prefix lengths always give different values.

## References

- Truth anchor: `D5/S3/Observer/Completion/InfiniteParityContinuityObstruction.finite_support_parity_has_no_continuous_completion`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast](../ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.md)
