# Maximal Control-Compatible Evaluation

## Abstract

The common coarsening of evaluation and control is the maximal control-compatible evaluation.

**Definition 1.1 (Fair evaluation kernel).**

Lean statement: `D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation.fairKernel`

*Formalization.* `D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation.fairKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fair kernel is the least equivalence relation containing both equality of full evaluations and equality of control readouts.

**Definition 1.2 (Fair evaluation).**

Lean statement: `D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation.fairEvaluation`

*Formalization.* `D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation.fairEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fair evaluation sends a state to its quotient class under the fair kernel. Its coordinate type is a quotient rather than the original evaluation codomain.

**Theorem 1.3 (The fair evaluation is the greatest common coarsening).**

$$\begin{gathered}\forall X, L, B, A: \operatorname{Type}, X \neq \varnothing,\\{}E_J: X \to L, C_{ctl}: X \to B, K: X \to A,\\{}J_{fair} \leq E_J \land\\{}J_{fair} \leq C_{ctl} \land\\{}(K \leq E_J \land K \leq C_{ctl}) \Rightarrow K \leq J_{fair}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation.maximal_control_compatible_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state type is explicitly nonempty so factor maps can be extended from reachable evaluation and control coordinates to their full codomains.

The first two public conjuncts state that the fair evaluation refines both the full evaluation and the control concept.

The third public conjunct states maximality: every candidate refining both source concepts factors through the same quotient. Mathlib's setoid supremum is exactly the required equivalence closure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation.fairEvaluation`
- Truth anchor: `D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation.fairKernel`
- Truth anchor: `D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation.maximal_control_compatible_evaluation`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
