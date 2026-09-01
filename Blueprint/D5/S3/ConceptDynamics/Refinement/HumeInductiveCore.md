# Hume Inductive Core

## Abstract

A constant finite past permits incompatible futures, while descent yields prediction.

**Theorem 1.1 (Finite past does not force a law, but descent yields prediction).**

$$\left(\left(\exists x \in Bool, y \in Bool,\; constantPast\left(x\right) = constantPast\left(y\right) \land identityFuture\left(x\right) \ne identityFuture\left(y\right)\right) \land \left(\neg \operatorname{Refines}\left(identityFuture, \operatorname{rangeFactorization}\left(constantPast\right)\right)\right)\right) \land \left(\forall X \in Type, H \in Type, Y \in Type, h \in \operatorname{Concept}\left(X, H\right), K \in \operatorname{Concept}\left(X, Y\right),\; \operatorname{FactorsThrough}\left(K, h\right) \Rightarrow \operatorname{Refines}\left(K, \operatorname{rangeFactorization}\left(h\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/HumeInductiveCore.hume_inductive_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The countermodel uses Boolean states. The readout constantPast maps both states to Unit, while identityFuture keeps them distinct. The displayed same-past and different-future witnesses therefore obstruct refinement.

The positive clause is general. Whenever a prediction is constant on the fibers of a history readout, it refines the canonical factorization through the realized history image.

Both clauses apply the frozen inductive-sufficiency equivalence directly. No alternative history, prediction, or refinement relation is defined.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/HumeInductiveCore.hume_inductive_core`
- Dependency: [D5/S3/ConceptDynamics/Refinement/InductiveSufficiency](InductiveSufficiency.md)
