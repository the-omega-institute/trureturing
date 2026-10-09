# Exact Causal Repair Error

## Abstract

Common causal envelopes give an optimal repair of a finite response table.

**Definition 1.1 (Feedback event distance).**

$$\forall T: \mathbb {N}, \forall A: (\operatorname {Fin}(T)) \to \operatorname {Type}(), \forall Y: (\operatorname {Fin}(T)) \to \operatorname {Type}(), [\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(A(t))], [\forall t: \operatorname {Fin}(T), \operatorname {Nonempty}(A(t))], [\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(Y(t))], \forall P: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, \forall Q: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, \operatorname {feedbackDistance}(P, Q) = \max _{f: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(Y, t.val)) \to A(t), E: \operatorname {Set}((t: \operatorname {Fin}(T)) \to Y(t))} \lvert \sum _{y: (t: \operatorname {Fin}(T)) \to Y(t), y \in E} (P(y)(\operatorname {feedbackActions}(f, y)) - Q(y)(\operatorname {feedbackActions}(f, y)))\rvert$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/CausalRepairEnvelopes.feedbackDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum ranges over every deterministic causal strategy and every event of complete output words. The response after feedback need not be normalized, so the quantity compares event masses.

**Definition 1.2 (Feedback normalization defect).**

$$\forall T: \mathbb {N}, \forall A: (\operatorname {Fin}(T)) \to \operatorname {Type}(), \forall Y: (\operatorname {Fin}(T)) \to \operatorname {Type}(), [\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(A(t))], [\forall t: \operatorname {Fin}(T), \operatorname {Nonempty}(A(t))], [\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(Y(t))], \forall P: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, \operatorname {feedbackDefect}(P) = \max _{f: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(Y, t.val)) \to A(t)} \lvert \operatorname {feedbackMass}(P, f) - 1\rvert$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/CausalRepairEnvelopes.feedbackDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defect is the largest absolute difference between a fed-back total mass and one.

**Theorem 1.3 (Attained optimal causal repair).**

$$\forall T: \mathbb {N}, \forall A: (\operatorname {Fin}(T)) \to \operatorname {Type}(), \forall Y: (\operatorname {Fin}(T)) \to \operatorname {Type}(), [\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(A(t))], [\forall t: \operatorname {Fin}(T), \operatorname {Nonempty}(A(t))], [\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(Y(t))], [\forall t: \operatorname {Fin}(T), \operatorname {Nonempty}(Y(t))], [\forall t: \operatorname {Fin}(T), \operatorname {DecidableEq}(Y(t))], (1 \leq T) \Rightarrow (\forall P: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, (\forall y: (t: \operatorname {Fin}(T)) \to Y(t), \forall a: (t: \operatorname {Fin}(T)) \to A(t), 0 \leq P(y)(a)) \Rightarrow ((\forall a: (t: \operatorname {Fin}(T)) \to A(t), \sum _{y: (t: \operatorname {Fin}(T)) \to Y(t)} P(y)(a) = 1) \Rightarrow (\exists Q: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, (\forall y: (t: \operatorname {Fin}(T)) \to Y(t), \forall a: (t: \operatorname {Fin}(T)) \to A(t), 0 \leq Q(y)(a)) \land (\forall a: (t: \operatorname {Fin}(T)) \to A(t), \sum _{y: (t: \operatorname {Fin}(T)) \to Y(t)} Q(y)(a) = 1) \land (\forall n: \mathbb {N}, (n \leq T) \Rightarrow (\forall x: \operatorname {Prefix}(Y, n), \forall a: (t: \operatorname {Fin}(T)) \to A(t), \forall b: (t: \operatorname {Fin}(T)) \to A(t), (\forall i: \operatorname {Fin}(T), (i.val < n) \Rightarrow (a(i) = b(i))) \Rightarrow (\operatorname {prefixMarginal}(Q, n, x, a) = \operatorname {prefixMarginal}(Q, n, x, b)))) \land (\operatorname {feedbackDistance}(P, Q) = \operatorname {feedbackDefect}(P)) \land (\forall R: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, (\forall y: (t: \operatorname {Fin}(T)) \to Y(t), \forall a: (t: \operatorname {Fin}(T)) \to A(t), 0 \leq R(y)(a)) \Rightarrow ((\forall a: (t: \operatorname {Fin}(T)) \to A(t), \sum _{y: (t: \operatorname {Fin}(T)) \to Y(t)} R(y)(a) = 1) \Rightarrow ((\forall n: \mathbb {N}, (n \leq T) \Rightarrow (\forall x: \operatorname {Prefix}(Y, n), \forall a: (t: \operatorname {Fin}(T)) \to A(t), \forall b: (t: \operatorname {Fin}(T)) \to A(t), (\forall i: \operatorname {Fin}(T), (i.val < n) \Rightarrow (a(i) = b(i))) \Rightarrow (\operatorname {prefixMarginal}(R, n, x, a) = \operatorname {prefixMarginal}(R, n, x, b)))) \Rightarrow (\operatorname {feedbackDefect}(P) \leq \operatorname {feedbackDistance}(P, R))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/CausalRepairEnvelopes.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonnegative finite response table normalized at each fixed action word admits a causal probability table with event distance exactly equal to its feedback normalization defect. Every other causal probability table has at least that distance.

Backward recursion takes the maximum and minimum, over the next action, of the sums of branch continuation masses. Tail strategies chosen independently on different output branches join into one causal strategy.

The forward upper construction pads the maximizing branch envelopes with nonnegative mass on a fixed output word. The lower construction scales the minimizing branch envelopes by the parent-to-child total-mass ratio; a zero denominator has zero parent mass.

A convex combination of these common envelopes has total mass one under every strategy. The feedback normalization criterion then gives prefix causality. Event discrepancies are bounded by the upper mass minus one and by one minus the lower mass; the complete output event supplies the matching universal lower bound.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/CausalRepairEnvelopes.feedbackDefect`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/CausalRepairEnvelopes.feedbackDistance`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/CausalRepairEnvelopes.result`
- Dependency: [D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion](FeedbackNormalizationCriterion.md)
