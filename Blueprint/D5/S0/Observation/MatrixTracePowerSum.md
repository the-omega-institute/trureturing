# Power Traces from Trace and Determinant in Size Two

## Abstract

Closed power traces for a two by two matrix from a supplied Vieta pair.

**Theorem 1.1 (A supplied Vieta pair gives every power trace).**

$$\begin{aligned}\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)],\\\forall M: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), R\right),\\\forall a, b: R,\\\forall k: \mathbb{N},\\(\operatorname{tr}\left(M\right) = a + b \land \operatorname{det}\left(M\right) = a \cdot b) \Rightarrow \operatorname{tr}\left(M^{k}\right) = a^{k} + b^{k}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/MatrixTracePowerSum.trace_pow_eq_add_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a two by two matrix has trace a + b and determinant a * b, then the trace of its k-th power is a ^ k + b ^ k.

No algebraically closed field is needed: the pair is supplied as a hypothesis rather than extracted from a characteristic polynomial, so the statement holds over any commutative ring in which such a pair happens to exist.

The proof starts from the size-two Cayley identity M ^ 2 = trace M • M - det M • 1, multiplies it by M ^ n, and reads off the resulting recurrence on traces.

A two-step induction then identifies that recurrence with the scalar power sums.

The frozen power_trace_characteristic_polynomial_saturation in this same directory already gives, for a field and any size, Cayley-Hamilton together with a recurrence among power traces; at size two that recurrence is the one used here, while this node adds the closed form and removes the field hypothesis, and that file is neither restated nor amended.

## References

- Truth anchor: `D5/S0/Observation/MatrixTracePowerSum.trace_pow_eq_add_pow`
