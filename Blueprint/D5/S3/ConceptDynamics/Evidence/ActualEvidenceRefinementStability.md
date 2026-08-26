# Actual Evidence Refinement Stability

## Abstract

Actual evidence fibers are nonempty, stable truth and falsity persist under refinement, and undecided evidence admits all three refinement outcomes.

**Theorem 1.1 (Actual refinement preserves stable knowledge).**

$$\forall X \in \operatorname{Type}\left(\right), B \in \operatorname{Type}\left(\right), BPrime \in \operatorname{Type}\left(\right), A \in X \to \operatorname{Prop}\left(\right), E \in X \to B, D \in X \to BPrime, P \in X \to \operatorname{Prop}\left(\right), a \in X,\; \left(A\left(a\right) \land \operatorname{Refines}\left(E, D\right)\right) \Rightarrow \left(\left(\exists x \in X,\; A\left(x\right) \land E\left(x\right) = E\left(a\right)\right) \land \left(\left(\exists x \in X,\; A\left(x\right) \land D\left(x\right) = D\left(a\right)\right) \land \left(\left(\left(\forall x \in X,\; \left(A\left(x\right) \land E\left(x\right) = E\left(a\right)\right) \Rightarrow P\left(x\right)\right) \Rightarrow \left(\forall x \in X,\; \left(A\left(x\right) \land D\left(x\right) = D\left(a\right)\right) \Rightarrow P\left(x\right)\right)\right) \land \left(\left(\left(\forall x \in X,\; \left(A\left(x\right) \land E\left(x\right) = E\left(a\right)\right) \Rightarrow \left(\neg P\left(x\right)\right)\right) \Rightarrow \left(\forall x \in X,\; \left(A\left(x\right) \land D\left(x\right) = D\left(a\right)\right) \Rightarrow \left(\neg P\left(x\right)\right)\right)\right) \land \left(\forall t \in X, f \in X,\; \left(A\left(t\right) \land \left(A\left(f\right) \land \left(E\left(t\right) = E\left(f\right) \land \left(P\left(t\right) \land \left(\neg P\left(f\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\left(\exists x \in X,\; A\left(x\right) \land \operatorname{pair}\left(E\left(x\right), x = t\right) = \operatorname{pair}\left(E\left(t\right), t = t\right)\right) \land \left(\forall x \in X,\; \left(A\left(x\right) \land \operatorname{pair}\left(E\left(x\right), x = t\right) = \operatorname{pair}\left(E\left(t\right), t = t\right)\right) \Rightarrow P\left(x\right)\right)\right) \land \left(\left(\left(\exists x \in X,\; A\left(x\right) \land \operatorname{pair}\left(E\left(x\right), x = f\right) = \operatorname{pair}\left(E\left(f\right), f = f\right)\right) \land \left(\forall x \in X,\; \left(A\left(x\right) \land \operatorname{pair}\left(E\left(x\right), x = f\right) = \operatorname{pair}\left(E\left(f\right), f = f\right)\right) \Rightarrow \left(\neg P\left(x\right)\right)\right)\right) \land \left(\exists x \in X, y \in X,\; A\left(x\right) \land \left(\operatorname{pair}\left(E\left(x\right), True\right) = \operatorname{pair}\left(E\left(t\right), True\right) \land \left(A\left(y\right) \land \left(\operatorname{pair}\left(E\left(y\right), True\right) = \operatorname{pair}\left(E\left(t\right), True\right) \land \left(P\left(x\right) \land \left(\neg P\left(y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Evidence/ActualEvidenceRefinementStability.actual_evidence_refinement_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public carrier has an admissibility predicate, coarse and refined concept readouts, a proposition on states, and an admissible actual anchor. Both actual fibers therefore expose their anchor witness and cannot be the impossible phase.

Stable truth and stable falsity are each written directly as universal claims on the admissible coarse fiber and transported to the admissible refined fiber. The proof applies the frozen robust-knowledge monotonicity theorem to the predicate and its negation.

For conflicting witnesses t and f in one coarse fiber, the displayed readouts pair the coarse evidence with x=t, x=f, or the always-true proposition. These shared constructions yield respectively a stably true, stably false, and still-undecided actual fiber.

Repository search found only the separate monotonicity, empty-fiber, and finite four-phase results. No exact theorem combined the unrestricted actual-anchor clauses and the three constructive outcomes.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Evidence/ActualEvidenceRefinementStability.actual_evidence_refinement_stability`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeRefinementMonotonicity](../Epistemic/RobustKnowledgeRefinementMonotonicity.md)
