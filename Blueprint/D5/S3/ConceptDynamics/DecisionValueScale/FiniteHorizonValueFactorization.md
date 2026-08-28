# Finite-Horizon Value Factorization

## Abstract

Compatible abstract dynamics factor every finite-horizon Bellman value.

**Theorem 1.1 (Every finite-horizon value factors through the abstraction).**

$$\begin{gathered}\forall X, Z, U: \operatorname{Type},\\{}C: Concept\left(X, Z\right), F: U \to \left(X \to X\right),\\{}G: U \to \left(Z \to Z\right), r: X \to \left(U \to \mathbb{R}\right),\\{}rbar: Z \to \left(U \to \mathbb{R}\right), q: X \to \mathbb{R},\\{}qbar: Z \to \mathbb{R},\\{}Fintype\left(U\right) \land Nonempty\left(U\right) \land\\{}(\forall u: U, x: X, C\left(F\left(u, x\right)\right) = G\left(u, C\left(x\right)\right)) \land\\{}(\forall x: X, u: U, r\left(x, u\right) = rbar\left(C\left(x\right), u\right)) \land\\{}(\forall x: X, q\left(x\right) = qbar\left(C\left(x\right)\right)) \Rightarrow\\{}\forall n: \mathbb{N}, finiteHorizonValue\left(F, r, q, n\right) = finiteHorizonValue\left(G, rbar, qbar, n\right) \circ C.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.finite_horizon_value_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The micro and macro state carriers share one finite nonempty action carrier. Their transitions commute with the concept map, while the stage reward and terminal value are evaluations of their macro counterparts.

The imported finiteHorizonValue primitive constructs both Bellman recurrences. The terminal equality starts the induction, and compatibility identifies every action score before the finite maxima are compared.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.finite_horizon_value_factorization`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent](../DecisionValue/FiniteHorizonOptimalActionDescent.md)
