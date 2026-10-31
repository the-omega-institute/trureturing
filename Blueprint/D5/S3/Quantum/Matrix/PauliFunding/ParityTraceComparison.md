# Even matrix traces and quadratic comparison

## Abstract

Quadratic characteristic roots compare every even power trace of a real two by two matrix.

Write evenMoment(alpha,beta,j)=(alpha+sqrt(alpha^2+beta))^(2j)+(alpha-sqrt(alpha^2+beta))^(2j), with the nonnegative real square root. The matrix W is arbitrary: symmetry, positivity and invertibility are not required. The parity control matrix is diag(1,-1).

**Theorem 1.1 (Vieta power traces).**

$$\forall W \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \left(0 \le beta \land \left(\operatorname{trace}\left(W\right) = 2 \cdot alpha \land \operatorname{det}\left(W\right) = 0 - beta\right)\right) \Rightarrow \left(\forall j \in \mathbb{N},\; \operatorname{trace}\left(W^{2 \cdot j}\right) = \operatorname{evenMoment}\left(alpha, beta, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison.even_trace_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative beta makes the characteristic roots real. Their sum and product are the supplied trace and determinant. The existing ring-general MatrixTracePowerSum.trace_pow_eq_add_pow then gives the identity, including beta=0 and repeated roots.

**Theorem 1.2 (A lower quadratic comparison).**

$$\forall W \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall c \in \mathbb{R},\; \left(\left(0 \le alpha \land 0 \le beta\right) \land \left(0 \le c \land \left(\operatorname{trace}\left(W\right) = 2 \cdot alpha \land \operatorname{det}\left(W\right) = 0 - beta\right)\right)\right) \Rightarrow \left(c^{2} - 2 \cdot alpha \cdot c - beta \le 0 \Rightarrow \left(\forall j \in \mathbb{N},\; c^{2 \cdot j} \le \operatorname{trace}\left(W^{2 \cdot j}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison.even_trace_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative c in the sublevel set c^2-2 alpha c-beta≤0 lies below the positive characteristic root. Taking the even power preserves this order, while the other root contributes a nonnegative even power. The order j may be zero.

**Theorem 1.3 (Strict comparison at every positive order).**

$$\forall W \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall c \in \mathbb{R},\; \left(\left(0 \le alpha \land 0 \le beta\right) \land \left(0 \le c \land \left(\operatorname{trace}\left(W\right) = 2 \cdot alpha \land \operatorname{det}\left(W\right) = 0 - beta\right)\right)\right) \Rightarrow \left(c^{2} - 2 \cdot alpha \cdot c - beta < 0 \Rightarrow \left(\forall j \in \mathbb{N},\; 1 \le j \Rightarrow c^{2 \cdot j} < \operatorname{trace}\left(W^{2 \cdot j}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison.even_trace_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A strictly negative characteristic polynomial places c strictly below the positive root. For j≥1 this gives a strict even-power inequality. The result applies to the parity transform of actual Pauli control resolvents, whose product moments are even powers of W.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison.even_trace_comparison`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison.even_trace_formula`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison.even_trace_strict`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../../S0/Observation/MatrixTracePowerSum.md)
