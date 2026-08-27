# Budget Knowledge Fiber Stability

## Abstract

Budget knowledge is exactly constancy on every joint-readout fiber.

**Theorem 1.1 (Budget knowledge is characterized by fiber stability).**

$$\forall X, O, B: \operatorname{Type},\\{}anchor: X, q: X \to O, P: X \to B,\\{}\operatorname{Knows}(q, P) \Leftrightarrow \forall x, y: X, q(x) = q(y) \Rightarrow P(x) = P(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EpistemicOperators/BudgetKnowledgeFiberStability.budget_knowledge_fiber_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state anchor is part of the prime-observer model. It supplies an actual predicate value, so a fiber-constant predicate can be extended from the realized readouts to the full readout type.

Budget knowledge uses the source definition: there is an observable on the joint-readout type whose pullback is the predicate. The displayed equivalence has one clause in each direction and no admissibility or finiteness premise.

The proof applies the exact repository factorization criterion, whose factorization step in turn reuses pinned Mathlib's Function.factorsThrough_iff.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EpistemicOperators/BudgetKnowledgeFiberStability.budget_knowledge_fiber_stability`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
