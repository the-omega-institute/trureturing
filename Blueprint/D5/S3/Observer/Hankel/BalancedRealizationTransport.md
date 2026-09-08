# BalancedRealizationTransport

## Abstract

Actual Gramians produce a balanced realization and a certified reduced system for the original behavior.

**Definition 1.1 (balanced A).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balancedA`

*Formalization.* `D5/S3/Observer/Hankel/BalancedRealizationTransport.balancedA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the transformed transition from the proved inverse balancing matrices.

**Definition 1.2 (balanced B).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balancedB`

*Formalization.* `D5/S3/Observer/Hankel/BalancedRealizationTransport.balancedB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the transformed input action.

**Definition 1.3 (balanced C).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balancedC`

*Formalization.* `D5/S3/Observer/Hankel/BalancedRealizationTransport.balancedC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the transformed output readout.

**Theorem 1.4 (balanced observability stein).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balanced_observability_stein`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedRealizationTransport.balanced_observability_stein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transports the exact observability Stein equality using the proved coordinate identities.

**Theorem 1.5 (balanced control stein).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balanced_control_stein`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedRealizationTransport.balanced_control_stein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transports the exact control Stein equality by the dual congruence.

**Theorem 1.6 (balanced stein).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balanced_stein`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedRealizationTransport.balanced_stein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives all premises of the previous balanced-truncation theorem from the transformed exact matrix equations.

**Theorem 1.7 (matrix State transport).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.matrixState_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedRealizationTransport.matrixState_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves equivalence of the actual forced state trajectories for every input and time.

**Theorem 1.8 (matrix Response transport).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.matrixResponse_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedRealizationTransport.matrixResponse_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves all-time equality of the original and balanced input-output behavior.

**Definition 1.9 (system Coordinates).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.systemCoordinates`

*Formalization.* `D5/S3/Observer/Hankel/BalancedRealizationTransport.systemCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the Gramians and balancing coordinates from the system itself under explicit power stability and joint readout injectivity assumptions.

**Theorem 1.10 (constructed reduction window bound).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.constructed_reduction_window_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedRealizationTransport.constructed_reduction_window_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

End-to-end finite-window error bound for the original system and a principal truncation of its constructed balanced realization.

**Theorem 1.11 (constructed reduction l2 bound).**

Lean statement: `D5/S3/Observer/Hankel/BalancedRealizationTransport.constructed_reduction_l2_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedRealizationTransport.constructed_reduction_l2_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

End-to-end total-energy error bound, with error summability proved, for the original system and the constructed reduced model.

## References

- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balancedA`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balancedB`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balancedC`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balanced_control_stein`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balanced_observability_stein`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.balanced_stein`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.constructed_reduction_l2_bound`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.constructed_reduction_window_bound`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.matrixResponse_transport`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.matrixState_transport`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedRealizationTransport.systemCoordinates`
- Dependency: [D5/S3/Observer/Hankel/BalancedTruncationTail](BalancedTruncationTail.md)
- Dependency: [D5/S3/Observer/Hankel/ExactGramianSeries](ExactGramianSeries.md)
