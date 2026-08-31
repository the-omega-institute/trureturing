# Chebyshev Transfer Trace

## Abstract

Powers of the free determinant-one transfer matrix realize Chebyshev traces.

**Definition 1.1 (Free transfer matrix).**

Lean statement: `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.freeTransferMatrix`

*Formalization.* `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.freeTransferMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a real spectral coordinate y, the named two-by-two matrix has rows (2y, -1) and (1, 0).

**Definition 1.2 (Chebyshev slack).**

Lean statement: `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.chebyshevSlack`

*Formalization.* `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.chebyshevSlack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At degree N and coordinate y, the named slack is one minus the square of the first-kind Chebyshev value.

**Theorem 1.3 (Determinant and half-trace invariants).**

$$\forall y \in \mathbb{R},\; \operatorname{det}\left(\operatorname{freeTransferMatrix}\left(y\right)\right) = 1 \land \frac{1}{2} \times \operatorname{tr}\left(\operatorname{freeTransferMatrix}\left(y\right)^{1}\right) = y$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.free_transfer_matrix_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct evaluation of the two-by-two determinant and trace gives determinant one and half-trace y.

**Theorem 1.4 (Transfer powers realize Chebyshev values).**

$$\forall N \in \mathbb{N}, y \in \mathbb{R},\; \frac{1}{2} \times \operatorname{tr}\left(\operatorname{freeTransferMatrix}\left(y\right)^{N}\right) = \operatorname{ChebyshevT}\left(N, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.chebyshev_transfer_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural degree, half the trace of the corresponding matrix power is the first-kind Chebyshev value.

The proof derives the quadratic transfer recurrence and matches its two initial values with Mathlib's Chebyshev recurrence.

**Theorem 1.5 (Transfer discriminant formula).**

$$\forall N \in \mathbb{N}, y \in \mathbb{R},\; \operatorname{discr}\left(\operatorname{freeTransferMatrix}\left(y\right)^{N}\right) = \operatorname{tr}\left(\operatorname{freeTransferMatrix}\left(y\right)^{N}\right)^{2} - 4$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.free_transfer_power_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's two-by-two characteristic-polynomial discriminant becomes the squared power trace minus four because every power has determinant one.

**Theorem 1.6 (Slack as a transfer discriminant).**

$$\forall N \in \mathbb{N}, y \in \mathbb{R},\; \operatorname{chebyshevSlack}\left(N, y\right) = -\frac{1}{4} \times (\operatorname{tr}\left(\operatorname{freeTransferMatrix}\left(y\right)^{N}\right)^{2} - 4)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.chebyshev_slack_eq_transfer_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the half-trace identity rewrites Chebyshev slack as minus one quarter of the transfer discriminant expression.

**Theorem 1.7 (Zero-degree and zero-coordinate audit).**

$$\frac{1}{2} \times \operatorname{tr}\left(\operatorname{freeTransferMatrix}\left(0\right)^{0}\right) = \operatorname{ChebyshevT}\left(0, 0\right) \land \left(\frac{1}{2} \times \operatorname{tr}\left(\operatorname{freeTransferMatrix}\left(0\right)^{1}\right) = \operatorname{ChebyshevT}\left(1, 0\right) \land \operatorname{chebyshevSlack}\left(0, 0\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.chebyshev_transfer_trace_degenerate_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete zero-coordinate audit checks the identity power at degree zero, the first power at degree one, and vanishing zero-degree slack.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.chebyshevSlack`
- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.chebyshev_slack_eq_transfer_discriminant`
- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.chebyshev_transfer_trace`
- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.chebyshev_transfer_trace_degenerate_cases`
- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.freeTransferMatrix`
- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.free_transfer_matrix_invariants`
- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.free_transfer_power_discriminant`
