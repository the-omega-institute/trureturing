# Fiber Modal Operator Laws

## Abstract

Fiber knowledge is an interior operator and fiber possibility its dual closure.

**Theorem 1.1 (Knowledge and possibility on concept fibers).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}C: Concept(X, B),\\{}\forall P: Set(X), a: X, a \in Knowledge(C, P) \iff \forall x: X, C(x) = C(a) \Rightarrow x \in P,\\{}\forall P: Set(X), a: X, a \in Possibility(C, P) \iff \exists x: X, C(x) = C(a) \land x \in P,\\{}(\forall P: Set(X), Knowledge(C, P) \subseteq P) \land\\{}(\forall P, Q: Set(X), P \subseteq Q \Rightarrow Knowledge(C, P) \subseteq Knowledge(C, Q)) \land\\{}(\forall P: Set(X), Knowledge(C, Knowledge(C, P)) = Knowledge(C, P)) \land\\{}(\forall P, Q: Set(X), Knowledge(C, intersection(P, Q)) = intersection(Knowledge(C, P), Knowledge(C, Q))) \land\\{}(\forall P: Set(X), P \subseteq Possibility(C, P)) \land\\{}(\forall P, Q: Set(X), P \subseteq Q \Rightarrow Possibility(C, P) \subseteq Possibility(C, Q)) \land\\{}(\forall P: Set(X), Possibility(C, Possibility(C, P)) = Possibility(C, P)) \land\\{}(\forall P: Set(X), Knowledge(C, P) = complement(Possibility(C, complement(P)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EpistemicOperators/FiberModalOperatorLaws.fiber_knowledge_and_possibility_operator_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readout C constructs both operators on the exact source carrier. Knowledge requires universal truth on the current readout fiber, while possibility requires an existential witness on that fiber.

The first four public clauses state factivity, monotonicity, idempotence, and conjunction preservation for knowledge. The next three state extensivity, monotonicity, and idempotence for possibility.

The final public clause is the classical complement duality. Its proof uses classical negation only in the direction from absence of a counterexample to universal fiber truth.

The proof imports the canonical fiber-knowledge primitive, its frozen partition-interior characterization, and the frozen topological knowledge laws rather than declaring another family primitive.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EpistemicOperators/FiberModalOperatorLaws.fiber_knowledge_and_possibility_operator_laws`
- Dependency: [D5/S3/ConceptDynamics/Epistemic/FiberInteriorEquivalence](../Epistemic/FiberInteriorEquivalence.md)
- Dependency: [D5/S3/ConceptDynamics/Epistemic/TopologicalKnowledgeOperator](../Epistemic/TopologicalKnowledgeOperator.md)
