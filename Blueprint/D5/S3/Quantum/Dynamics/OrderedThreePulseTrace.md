# Ordered Three-Pulse Trace

## Abstract

Ordered three-pulse trace deviation has a dimension-free Frobenius bound.

**Definition 1.1 (The matrix pulse integral).**

$$D_{X}(s) = \int_{0}^{1}\exp{i r s X} X dr$$

*Formalization.* `D5/S3/Quantum/Dynamics/OrderedThreePulseTrace.pulse0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite index type, complex square matrix X and real s, the pulse is the interval integral of exp(i r s X) X over 0 <= r <= 1. The matrix product keeps X on the right.

**Theorem 1.2 (Ordered three-pulse real trace bound).**

$$\begin{gathered}\forall (I: Type) [\operatorname{Fintype}(I)] [\operatorname{DecidableEq}(I)],\\\forall A, B, C: Mat_{I}(\mathbb{R}), \forall L, t: \mathbb{R},\\A^{T} = A \land B^{T} = B \land C^{T} = C \land\\0 \leq L \land \Vert A \Vert_{F} \leq L \land \Vert B \Vert_{F} \leq L \land \Vert C \Vert_{F} \leq L \land 0 < t \Rightarrow\\{}[(\forall X: Mat_{I}(\mathbb{C}), D_{X}(0) = X) \land\\(\forall X: Mat_{I}(\mathbb{C}), \forall s: \mathbb{R}, s \neq 0 \Rightarrow D_{X}(s) = \frac{\exp{i s X} - I}{i s}) \land\\|\Re \operatorname{Tr}_{\mathbb{C}}(D_{A_{\mathbb{C}}}(t) D_{B_{\mathbb{C}}}(t) D_{C_{\mathbb{C}}}(t)) - \operatorname{Tr}_{\mathbb{R}}(A B C)| \leq \frac{5}{4} L^{5} t^{2}]\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OrderedThreePulseTrace.ordered_three_pulse_real_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index type is any finite type, including the empty type. A, B and C are real symmetric square matrices with their actual Frobenius norms at most L, where L is nonnegative; t is positive. No pairwise commutation is assumed.

The same theorem proves D_X(0) = X and, for every nonzero real s, D_X(s) = (exp(i s X) - I)/(i s), even for arbitrary complex X. In the trace bound each real matrix is entrywise complexified; the three pulse factors remain in A, B, C order.

The proof uses the existing GNS Frobenius norm-square trace identity, unitary matrix exponentials, two derivatives of the ordered product, and the nine-term second-derivative estimate. The latter is at most 5 L^5/2; the zero derivative of the real trace at zero gives the 5 L^5 t^2/4 remainder. The quotient identity follows from the interval fundamental theorem of calculus.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/OrderedThreePulseTrace.ordered_three_pulse_real_trace_bound`
- Truth anchor: `D5/S3/Quantum/Dynamics/OrderedThreePulseTrace.pulse0`
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)
