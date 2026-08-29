# Singleton Relative Complement Criterion

## Abstract

A singleton relative complement exists exactly when the ambient set is the corresponding two-point set.

**Theorem 1.1 (A singleton relative complement characterizes a two-point ambient set).**

$$\forall X: \operatorname{Type}, Omega: \operatorname{Set}\left(X\right), t: X, t \in Omega \Rightarrow (\exists s: X, s \in Omega \land s \neq t \land Omega \setminus \{t\} = \{s\}) \iff (\exists s: X, s \in Omega \land s \neq t \land Omega = \{t, s\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InvolutionLogic/SingletonRelativeComplementCriterion.singleton_relative_complement_iff_two_point_universe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a point t in an ambient set Omega. If removing t leaves exactly one distinct point s, every ambient point is t or s.

Conversely, if Omega consists of the distinct points t and s, removing t leaves exactly the singleton containing s.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InvolutionLogic/SingletonRelativeComplementCriterion.singleton_relative_complement_iff_two_point_universe`
- Dependency: [D5/S3/ConceptDynamics/InvolutionLogic/RelativeNegation](RelativeNegation.md)
