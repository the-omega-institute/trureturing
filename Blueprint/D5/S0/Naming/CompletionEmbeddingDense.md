# Density of the Canonical Completion Map

## Abstract

The canonical map from a metric space into its completion has dense range.

**Theorem 1.1 (The canonical completion map has dense range).**

$$\forall N [\operatorname{MetricSpace}(N)],\\\operatorname{DenseRange}(coe_{N}: N \to \operatorname{Completion}(N)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/CompletionEmbeddingDense.completion_embedding_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every metric space N, its canonical coercion into the uniform-space completion has dense range. The source assumptions of countability, absence of isolated points, incompleteness, and a measure are not needed for this density clause.

Pinned Mathlib was queried for denseRange_coe, DenseRange Completion, completion dense, canonical embedding, and Completion coe. It supplies the exact density result as UniformSpace.Completion.denseRange_coe. The Lean declaration is therefore a thin wrapper with no replacement proof.

This document partially closes clause (i) only. Clause (ii), asserting no isolated points together with meagerness of the image and comeagerness of its complement, remains unresolved. Clause (iii), asserting full measure of the complement for an atomless Borel probability measure, also remains unresolved.

## References

- Truth anchor: `D5/S0/Naming/CompletionEmbeddingDense.completion_embedding_dense`
