# Residual Complement of the Canonical Completion Image

## Abstract

A countable perfect metric space has a negligible image in its completion.

**Theorem 1.1 (The canonical completion image has residual full-measure complement).**

$$\forall N, \mu,\\[\operatorname{MetricSpace}(N)], [\operatorname{Countable}(N)], [\operatorname{PerfectSpace}(N)],\\[\operatorname{NoAtoms}(\mu)], [\operatorname{IsProbabilityMeasure}(\mu)],\\\operatorname{DenseRange}(coe_{N}) \land\\\operatorname{PerfectSpace}(\operatorname{Completion}(N)) \land\\\operatorname{IsMeagre}(\operatorname{range}(coe_{N})) \land\\\mu(\operatorname{Completion}(N) \setminus \operatorname{range}(coe_{N}))=1.$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Conservation/CompletionEmbeddingResidual.completion_embedding_residual_full_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absence of isolated points is assumed for N and proved for its completion. Density alone is clause (i), already carried by the frozen CompletionEmbeddingDense declaration.

The proof transfers preperfectness through the canonical embedding. Its dense closure is the whole completion, so the completion is a perfect space. Countability then writes the image as a countable union of nowhere-dense singletons.

An atomless measure assigns zero measure to the countable image. Probability normalization therefore gives measure one to its complement.

This declaration discharges clauses (ii) and (iii). It does not claim coverage of the residual atom. D5-T0032 remains open because the existing formalization receipt is misbound and may be corrected only through the receipt-correction door.

## References

- Truth anchor: `D5/S0/Naming/Conservation/CompletionEmbeddingResidual.completion_embedding_residual_full_measure`
- Dependency: [D5/S0/Naming/CompletionEmbeddingDense](../CompletionEmbeddingDense.md)
