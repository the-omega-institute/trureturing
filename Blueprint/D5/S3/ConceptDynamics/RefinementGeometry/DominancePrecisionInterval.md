# Dominance Precision Interval

## Abstract

Complete dominance occupies exactly the half-open band between the two pairwise reveal thresholds.

**Theorem 1.1 (Complete dominance is an interval of precision levels).**

$$\begin{aligned}\forall X: \operatorname{Type}, O: \mathbb{N} \to \operatorname{Type},\\q: \forall k: \mathbb{N}, X \to O_{k},\\rho: \forall k: \mathbb{N}, O_{k+1} \to O_{k},\\x_{AA}, x_{AB}, x_{BB}: X,\\(\forall k: \mathbb{N}, q_{k} = rho_{k} \circ q_{k+1}) \Rightarrow\\\operatorname{let} r_{1} : = \operatorname{revealThreshold}\left(O, q, x_{AA}, x_{AB}\right),\\r_{2} : = \operatorname{revealThreshold}\left(O, q, x_{AB}, x_{BB}\right),\\d(k) : = (q_{k}(x_{AA}) = q_{k}(x_{AB}) \land q_{k}(x_{AB}) \neq q_{k}(x_{BB})),\\D : = \{v\in \operatorname{WithTop}\left(\mathbb{N}\right) \mid \exists k\in \mathbb{N}, v = k \land d(k)\},\\D_{fin} : = \{k\in \mathbb{N} \mid d(k)\},\\W_{dom} : = \operatorname{ncard}\left(D_{fin}\right) \operatorname{in}\\(\forall k\in \mathbb{N}, d(k) \Leftrightarrow r_{2} \leq k \land k < r_{1}) \land\\D = \operatorname{Ico}\left(r_{2}, r_{1}\right) \land\\((\exists k\in \mathbb{N}, d(k)) \Leftrightarrow r_{2} < r_{1}) \land\\(\forall n_{1}, n_{2}\in \mathbb{N}, r_{1} = n_{1} \land r_{2} = n_{2} \Rightarrow W_{dom} = n_{1} - n_{2}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/DominancePrecisionInterval.dominance_precision_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reveal threshold of a pair is constructed as its least separating precision, with infinity used exactly when no precision separates the pair. Compatibility of the lowering maps makes separation persistent above that threshold.

Complete dominance at level k is the simultaneous agreement of AA with AB and separation of AB from BB. Consequently its extended-natural levels are precisely the half-open interval from r2 to r1, and such a level exists exactly when r2 is strictly below r1.

The finite dominance width is constructed as the cardinality of the finite-level dominance band. When both reveal thresholds are finite, the natural interval cardinality theorem identifies it with n1 - n2.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/DominancePrecisionInterval.dominance_precision_interval`
- Dependency: [D5/S3/ConceptDynamics/RefinementGeometry/PrecisionSeparationPersistence](PrecisionSeparationPersistence.md)
