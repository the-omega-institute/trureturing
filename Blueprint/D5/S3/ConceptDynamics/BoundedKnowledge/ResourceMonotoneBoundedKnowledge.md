# Resource-Monotone Bounded Knowledge

## Abstract

Uniform bounded knowledge is monotone in resources and refines structural knowledge.

**Theorem 1.1 (Bounded knowledge is monotone in the resource budget).**

$$\forall X, B, R: \operatorname{Type},\ \operatorname{Preorder}\left(R\right), P: R \to \operatorname{Set}\left(B \to Prop\right),\ \operatorname{Monotone}\left(P\right), A: X \to Prop, e: X \to B,\ K: X \to Prop, a: X, r, s: R,\ r \leq s \Rightarrow \operatorname{boundedKnowledge}\left(P, A, e, K, a, r\right) \Rightarrow \operatorname{boundedKnowledge}\left(P, A, e, K, a, s\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge.resource_monotone_bounded_knowledge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A budget r exposes a set P(r) of classifiers on evidence values. The hypothesis that P is monotone means that every classifier available at r remains available at each larger budget s.

Bounded knowledge supplies an admissible true anchor and one classifier that decides the predicate uniformly from the evidence readout. When r is at most s, monotonicity transports that classifier to P(s), while the anchor and uniformity witnesses are unchanged.

**Theorem 1.2 (Bounded knowledge implies structural knowledge).**

$$\forall X, B, R: \operatorname{Type},\ P: R \to \operatorname{Set}\left(B \to Prop\right), A: X \to Prop, e: X \to B,\ K: X \to Prop, a: X, r: R,\ \operatorname{boundedKnowledge}\left(P, A, e, K, a, r\right) \Rightarrow \operatorname{structuralKnowledge}\left(A, e, K, a\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge.bounded_knowledge_implies_structural_knowledge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bounded classifier depends only on the evidence value. Two states in the same evidence fiber therefore receive the same classifier output, so the predicate has the same truth value at both states.

The admissibility and truth clauses at the anchor pass through directly. The uniform classifier supplies the remaining fiber-constancy clause of structural knowledge.

**Theorem 1.3 (Structural knowledge need not be bounded knowledge).**

$$\begin{gathered}X = Bool, B = Unit, R = Nat,\\{}\operatorname{structuralKnowledge}\left(\operatorname{const}\left(True\right), \operatorname{const}\left(unit\right), \operatorname{const}\left(True\right), true\right) \land \neg \operatorname{boundedKnowledge}\left(\operatorname{const}\left(\emptyset\right), \operatorname{const}\left(True\right), \operatorname{const}\left(unit\right), \operatorname{const}\left(True\right), true, 0\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge.structural_knowledge_not_bounded_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness uses Boolean states, the one-point Unit evidence type, and constant-true admissibility and predicate functions. The predicate is constant on the sole evidence fiber, so structural knowledge holds at the anchor true.

The resource type is Nat and every budget exposes the empty set of classifiers Unit -> Prop. In particular, budget zero has no uniform classifier, so bounded knowledge fails. This concrete witness disproves the converse implication.

## References

- Truth anchor: `D5/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge.bounded_knowledge_implies_structural_knowledge`
- Truth anchor: `D5/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge.resource_monotone_bounded_knowledge`
- Truth anchor: `D5/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge.structural_knowledge_not_bounded_counterexample`
