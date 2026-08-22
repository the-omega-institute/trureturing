# Safe Answer Coverage Maximality

## Abstract

The canonical safe answer is zero-error and covers every zero-error answer on an inhabited fiber, while an empty fiber supplies the necessary counterexample.

**Lemma 1.1 (The canonical safe answer has zero error).**

$$\forall X \in Type, B \in Type, Y \in Type, A \in X \to Prop, C \in X \to B, T \in X \to Y,\; \operatorname{ZeroError}\left(A, C, T, \operatorname{canonicalSafeAnswer}\left(A, C, T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality.canonical_safe_answer_zero_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical answerer responds at a concept value only when the admitted inputs in that fiber attain one unique target. Every admitted input contributes its own target to the fiber, so uniqueness forces the chosen answer to equal that target. Thus every answer it makes is correct.

**Theorem 1.2 (The canonical safe answer covers every safe inhabited-fiber answer).**

$$\forall X \in Type, B \in Type, Y \in Type, A \in X \to Prop, C \in X \to B, T \in X \to Y, g \in B \to \operatorname{Option}\left(Y\right), b \in B, y \in Y,\; \left(\operatorname{ZeroError}\left(A, C, T, g\right) \land \left(\left(\exists x \in X,\; A\left(x\right) \land C\left(x\right) = b\right) \land g\left(b\right) = \operatorname{some}\left(y\right)\right)\right) \Rightarrow \operatorname{canonicalSafeAnswer}\left(A, C, T, b\right) = \operatorname{some}\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality.safe_answer_coverage_maximality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a zero-error answerer returns y at b and some admitted input lies over b. Zero error identifies that input's target with y.

Any two targets attained in the same fiber are witnessed by admitted inputs receiving the same answer y. Zero error therefore forces both targets to equal y, making the fiber the singleton {y}. The canonical answerer consequently returns y as well.

**Lemma 1.3 (An empty fiber defeats unconditional coverage).**

$$\exists A \in \operatorname{Fin}\left(1\right) \to Prop, C \in \operatorname{Fin}\left(1\right) \to Bool, T \in \operatorname{Fin}\left(1\right) \to Bool, g \in Bool \to \operatorname{Option}\left(Bool\right), b \in Bool, y \in Bool,\; \operatorname{ZeroError}\left(A, C, T, g\right) \land \left(\left(\neg \left(\exists x \in \operatorname{Fin}\left(1\right),\; A\left(x\right) \land C\left(x\right) = b\right)\right) \land \left(g\left(b\right) = \operatorname{some}\left(y\right) \land \operatorname{canonicalSafeAnswer}\left(A, C, T, b\right) = none\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality.empty_fiber_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take one admitted input with concept value false and target false, and let the competing answerer return each Boolean observation itself. It has zero error on the only inhabited fiber. At true, however, the fiber is empty: the competing answerer returns true while the canonical answerer abstains. Hence the inhabitation premise in the maximality theorem cannot be removed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality.canonical_safe_answer_zero_error`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality.empty_fiber_counterexample`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality.safe_answer_coverage_maximality`
