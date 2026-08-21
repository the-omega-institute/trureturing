# Inverse-Limit Descent and Reverse Criterion

## Abstract

Compatible finite-stage maps induce a unique map on inverse-limit families, and surjective coordinates recover finite naturality.

**Theorem 1.1 (Inverse-limit maps descend uniquely and reflect finite naturality).**

$$\forall I, S, T, delta, \operatorname{Compatible}(S, T, delta) \Rightarrow (\exists! D: \operatorname{CompatibleStageFamily}(S) \Rightarrow \operatorname{CompatibleStageFamily}(T), \forall a, i, Delta(a)_{i} = delta_{i}(a_{i}) \land \forall D: \operatorname{CompatibleStageFamily}(S) \Rightarrow \operatorname{CompatibleStageFamily}(T), (\forall a, i, Delta(a)_{i} = delta_{i}(a_{i})) \Rightarrow (\forall i, \operatorname{Surjective}(a_{i})) \Rightarrow \forall h, x, \operatorname{restrict}(T, h, delta_{j}(x)) = delta_{i}(\operatorname{restrict}(S, h, x))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/InverseLimitDescent.inverse_limit_descent_and_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source and target are inverse-stage systems with restriction channels satisfying identity and composition. A stage map is assumed to commute with every restriction channel.

The induced map sends a compatible source family to the family obtained by applying the corresponding stage map at every coordinate. The public statement includes both its coordinate equation and uniqueness.

Conversely, if every source coordinate is surjective from compatible families and a map with the displayed coordinate equation exists, evaluating compatibility on a lifted family recovers strict finite-stage naturality.

The proof reuses the canonical InverseStageSystem and CompatibleStageFamily types from CompletionIsomorphismCriterion. Repository search found no existing theorem packaging this induced map with the reverse clause.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/InverseLimitDescent.inverse_limit_descent_and_reverse`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion](CompletionIsomorphismCriterion.md)
