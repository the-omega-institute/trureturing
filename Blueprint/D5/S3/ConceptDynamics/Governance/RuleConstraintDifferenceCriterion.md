# Rule Constraint and Arbitrary Differences

## Abstract

Rule factorization excludes arbitrary differences, with the converse isolated to finite effective models.

**Theorem 1.1 (Rule constraint excludes arbitrary differences).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}A: X \to B, J: X \to Y,\\{}((\exists j: B \to Y, J = j \circ A) \Rightarrow (\neg \exists x, y: X, A(x) = A(y) \land J(x) \neq J(y))) \land\\{}(\forall [\operatorname{Fintype}(X)], [\operatorname{Fintype}(B)], [\operatorname{Fintype}(Y)],\\{}\operatorname{Surjective}(A) \Rightarrow (\neg \exists x, y: X, A(x) = A(y) \land J(x) \neq J(y)) \Rightarrow (\exists j: B \to Y, J = j \circ A)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/RuleConstraintDifferenceCriterion.rule_constraint_difference_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward clause is unrestricted. If the decision J factors through the public attribute readout A, two cases with the same public attribute cannot receive different decisions.

The converse has its own premise set: the state, attribute, and decision carriers are finite, and A is surjective so its codomain consists only of effective public values. Under those restrictions, absence of an arbitrary-difference pair yields a public rule factorization.

The repository's frozen answerability criterion is applied directly in the inhabited case. If the state carrier is empty, surjectivity forces the attribute carrier to be empty and the factorization is constructed by empty elimination.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/RuleConstraintDifferenceCriterion.rule_constraint_difference_criterion`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
