# Finite Prefix Compactness

## Abstract

Finite realizability of every horizon forces one compatible infinite path.

**Theorem 1.1 (Finite prefixes give a global path).**

$$\operatorname{FinitePrefixRealizable}\left(R\right) \Rightarrow \operatorname{GlobalPath}\left(R\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/FinitePrefixCompactness.exists_global_path_of_finite_prefixes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each time index has a finite discrete alphabet, and R records the allowed transition to the next index.

The N-prefix conditions form a decreasing sequence of nonempty closed subsets of the compact product. Cantor intersection compactness supplies a point in every stage, hence a path satisfying every transition.

This is the finite-prefix to infinite-path bridge used when extending symbolic or finite-state constructions to an actual infinite object.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/FinitePrefixCompactness.exists_global_path_of_finite_prefixes`
