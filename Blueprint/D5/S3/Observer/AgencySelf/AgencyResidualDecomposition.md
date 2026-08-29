# Agency Residual Decomposition

## Abstract

The current-state kernel decomposes into completed and strategy-residual pairs.

**Theorem 1.1 (The current relation splits into completed or residual pairs).**

$$\forall current: H \to M, profile: H \to P, x, y: H, \operatorname{SameUnder}\left(current, x, y\right) \iff (\operatorname{CompletionRelated}\left(current, profile, x, y\right) \lor \operatorname{AgencyResidual}\left(current, profile, x, y\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyResidualDecomposition.current_relation_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix current and profile readouts and two histories. Equality under the current readout admits a case split on profile equality.

If profile values agree, the pair is completion-related; otherwise it lies in the agency residual. Either branch retains current-state equality.

The disjunction is exhaustive for the displayed pair and makes no claim that one branch is globally inhabited.

**Theorem 1.2 (Completed and residual pairs are disjoint).**

$$\forall current: H \to M, profile: H \to P, x, y: H, \neg(\operatorname{CompletionRelated}\left(current, profile, x, y\right) \land \operatorname{AgencyResidual}\left(current, profile, x, y\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyResidualDecomposition.completion_residual_exclusive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A completion-related pair has equal profile values, whereas an agency residual pair has unequal profile values.

The same pair cannot satisfy both predicates, so their conjunction is logically impossible.

## References

- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyResidualDecomposition.completion_residual_exclusive`
- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyResidualDecomposition.current_relation_decomposition`
