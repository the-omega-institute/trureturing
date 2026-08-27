# Finite Intervention Sequence Commutation

## Abstract

One-step commuting intervention squares commute along every finite action list.

**Theorem 1.1 (Atomic commuting squares preserve every finite intervention path).**

$$\forall U \in Type, X \in Type, Z \in Type, C \in X \to Z, F \in U \to \left(X \to X\right), G \in U \to \left(Z \to Z\right),\; \left(\forall u \in U, x \in X,\; C\left(F\left(u\right)\left(x\right)\right) = G\left(u\right)\left(C\left(x\right)\right)\right) \Rightarrow \left(\forall alpha \in \operatorname{List}\left(U\right),\; C \circ (x \mapsto \operatorname{foldl}\left((x, u \mapsto F\left(u\right)\left(x\right)), x, alpha\right)) = (z \mapsto \operatorname{foldl}\left((z, u \mapsto G\left(u\right)\left(z\right)), z, alpha\right)) \circ C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionsExchange/FiniteInterventionSequenceCommutation.finite_intervention_sequences_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The micro and macro action families act on their respective source and abstract carriers. Each action makes the abstraction square commute.

Both finite sequence maps are the public left folds of those action families. List induction transports the atomic equation through the remaining macro fold, yielding the displayed composite-map equality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionsExchange/FiniteInterventionSequenceCommutation.finite_intervention_sequences_commute`
