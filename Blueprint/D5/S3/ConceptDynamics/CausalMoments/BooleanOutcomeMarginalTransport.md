# BooleanOutcomeMarginalTransport

## Abstract

Finite rational nonfair outcome transport on the original complete-mediation model.

All theorem entries are bound to their Lean declarations without formula projection. The original mediator and outcome probability-law semantics are retained. No compilation or independent review status is asserted by this source document.

**Definition 1.1 (Actual outcome coordinate mean).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.tableMean`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.tableMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is the original finite-law success expectation, with the complete response table retained.

**Theorem 1.2 (Every coordinate mean is a probability).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.tableMean_mem`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.tableMean_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative normalized original weights imply zero-to-one bounds, including deterministic coordinates.

**Definition 1.3 (Monotone Bernoulli transition rates).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.bitTransition`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.bitTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upward branch flips original zero bits; the downward branch thins original one bits. The unused branch remains defined at source mean zero or one.

**Theorem 1.4 (Preserve the original law and attain every minimum mismatch).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.exists_exact_marginal_transport`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.exists_exact_marginal_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One joint old/new table law preserves every original-table expectation, realizes all target means, and has coordinate mismatch exactly the absolute mean difference. Original outcome coordinates need not be independent. The auxiliary table is independent of the whole original law.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.bitTransition`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.exists_exact_marginal_transport`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.tableMean`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.tableMean_mem`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable](FiniteConditionalResponseTable.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification](ProductLawMomentSparsification.md)
