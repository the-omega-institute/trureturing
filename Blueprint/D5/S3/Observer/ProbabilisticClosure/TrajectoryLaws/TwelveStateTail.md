# Explicit tails of the original twelve-state law

## Abstract

Explicit tails of the original twelve-state law

**Theorem 1.1 (A specified affinity bound controls surviving pairs).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.specified_survival`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.specified_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite binary unifilar probability kernel p with successor delta, nonnegative rho and a common length-two full-word affinity bound rho for every distinct pair, the killed-pair survivingAffinity at every radius r is at most rho^(r/2). The proof uses the existing matrix_block supplier. TwelveStateFutureRecovery consumes this same helper for the actual six-label dynamic kernel.

All probabilities and conditional losses in this document use the original twelve-state parameter, its selected bilateral jointLaw and its visible marginal. Positive-support trimming is only a proved reindexing of this same all-positive producer. The target of classError is the original class at time zero, estimated from coordinates -r through -1; it does not move with the radius.

**Definition 1.2 (The exact retained quotient has six labels).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.labelEquiv`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.labelEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

labelEquiv is an equivalence from the future classes of trim(parameter) to Bool times Fin 3. Each class maps to the original phase and index modulo three. The proof reindexes every marked word matrix along the bijection from retained positive states to all twelve original states, identifies their full finite future laws, and then uses the actual future_classes theorem. The original lifts are preserved until the proved quotient identification.

**Definition 1.3 (The actual explicit affinity constant).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.rho`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rho is sqrt(15)/4.

**Theorem 1.4 (Actual geometric losses and a finite erasure allowance).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.actual_explicit_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.actual_explicit_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual constant rho is nonnegative and strictly below one. For every natural radius r, classError(parameter,r) is at most ofReal((5/2)*rho^(r/2)); both real half-line risks leftRisk(parameter,r) and rightRisk(parameter,r) have that same bound. For every natural R, the actual possibly infinite erasureTail(parameter,R) is at most ofReal(10/(1-rho)*rho^(R/2)). The ENNReal sum of all fixed-target classError(parameter,r) is finite. Natural division is floor division. The exact two-word affinity passes to the actual six-class quotient, matrix_block gives the same explicit killed-pair bound, actual_map_pairs supplies the actual fixed-target loss, and the six-class cardinal bound gives D at most 5/2. The original full-half-line erasure comparison and tail_series supply the final allowance. This statement does not assert the separate persistent-hidden-entropy identity or the full erased-bit recovery theorem.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.actual_explicit_tail`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.labelEquiv`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.rho`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail.specified_survival`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail](OriginalUnifilarErasureTail.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStatePresentation](TwelveStatePresentation.md)
