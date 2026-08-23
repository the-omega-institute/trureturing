# Mixed-Fiber Zero Error Is Impossible

## Abstract

Opposite labels in one evidence fiber force a sharp one-error lower bound for every deterministic evidence-based decision rule.

**Theorem 1.1 (A mixed evidence fiber rules out zero error).**

$$\forall X \in Type, B \in Type, e \in X \to B, l \in X \to Bool, x \in X, y \in X,\; \left(e\left(x\right) = e\left(y\right) \land \left(l\left(x\right) = true \land l\left(y\right) = false\right)\right) \Rightarrow \left(\forall d \in B \to Bool,\; d\left(e\left(x\right)\right) \ne l\left(x\right) \lor d\left(e\left(y\right)\right) \ne l\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/MixedFiberZeroErrorImpossible.mixed_fiber_zero_error_impossible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evidence map sends x and y to the same observation, while their Boolean labels are true and false. A deterministic rule therefore returns the same value at both states and cannot agree with both opposite labels; at least one state must be misclassified.

Because the conclusion ranges over every total evidence-based rule, the obstruction belongs to the evidence interface itself rather than to a particular choice of decision procedure.

**Lemma 1.2 (The one-error lower bound is sharp).**

$$\forall X \in Type, B \in Type, e \in X \to B, l \in X \to Bool, x \in X, y \in X,\; \left(e\left(x\right) = e\left(y\right) \land \left(l\left(x\right) = true \land l\left(y\right) = false\right)\right) \Rightarrow \left(\left(\forall d \in B \to Bool,\; 1 \le \operatorname{pairErrorCount}\left(e, l, d, x, y\right)\right) \land \left(\exists d \in B \to Bool,\; \operatorname{pairErrorCount}\left(e, l, d, x, y\right) = 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/MixedFiberZeroErrorImpossible.mixed_fiber_error_bound_is_tight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Counting errors on the ordered pair (x, y), the mixed-fiber theorem gives a lower bound of one for every deterministic rule. The constant-true rule is correct on the positively labelled state and wrong on the negatively labelled state, so it attains exactly one error. Thus the universal lower bound cannot be improved.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/MixedFiberZeroErrorImpossible.mixed_fiber_error_bound_is_tight`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/MixedFiberZeroErrorImpossible.mixed_fiber_zero_error_impossible`
