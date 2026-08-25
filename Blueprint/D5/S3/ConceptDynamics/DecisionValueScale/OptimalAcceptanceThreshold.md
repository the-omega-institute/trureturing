# Optimal Acceptance Threshold

## Abstract

Binary expected-loss comparison is equivalent to the optimal acceptance threshold.

**Theorem 1.1 (Acceptance threshold).**

$$\forall p, c_{FP}, c_{FN} \in \mathbb{R}, 0 < c_{FP} \land 0 < c_{FN} \Rightarrow ((1 - p) c_{FP} \leq p c_{FN} \iff p \geq \frac{c_{FP}}{c_{FP} + c_{FN}}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValueScale/OptimalAcceptanceThreshold.optimal_acceptance_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The posterior probability p and both error costs are real, with strictly positive false-positive and false-negative costs.

Accepting has expected loss (1-p)c_FP, while rejecting has expected loss p c_FN. Their direct comparison is equivalent to p reaching the displayed cost threshold.

Repository and pinned Mathlib searches found no exact theorem combining this source loss comparison with the threshold equivalence.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValueScale/OptimalAcceptanceThreshold.optimal_acceptance_threshold`
