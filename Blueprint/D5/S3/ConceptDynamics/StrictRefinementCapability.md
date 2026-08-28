# Strict Refinement Capability

## Abstract

Effective strict refinement creates a new question and a new differentiating policy.

**Theorem 1.1 (Strict refinement yields question and policy capability).**

$$\forall X, C, D, U: Type,\ q_{C}: X \to C, q_{D}: X \to D, \operatorname{Surjective}\left(q_{C}\right) \land \operatorname{Surjective}\left(q_{D}\right) \land \operatorname{StrictRefinement}\left(q_{C}, q_{D}\right) \land \exists u_{0}: U, u_{1}: U, u_{0} \neq u_{1} \Rightarrow ((\exists Q: X \to Bool, ((\exists! a: D \to Bool, Q = a \circ q_{D}) \land \neg(\exists b: C \to Bool, Q = b \circ q_{C}))) \land (\exists Pi: X \to U, ((\exists! p: D \to U, Pi = p \circ q_{D}) \land \neg(\exists c: C \to U, Pi = c \circ q_{C})))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/StrictRefinementCapability.strict_refinement_capability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Effective concepts are represented by surjective readouts. Strict refinement is the public factorization relation from the existing ConceptDynamics order, together with failure of reverse refinement.

The conclusion contains both source clauses: a Boolean question and a policy into the action set each have a unique factor through the finer readout and no factor through the coarser readout.

The separating pair is obtained from strictness and effective readouts; the two distinct actions then provide the policy witnesses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/StrictRefinementCapability.strict_refinement_capability`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](ConceptJoinUniversal.md)
