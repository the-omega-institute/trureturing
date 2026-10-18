# Power Traces from Trace and Determinant in Size Two

## Abstract

Closed power traces for a two by two matrix from a supplied Vieta pair.

**Theorem 1.1 (The matrix power recurrence in size two).**

$$\begin{aligned}\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)],\\\forall M: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), R\right), n: \mathbb{N},\\M^{n + 2} = \operatorname{tr}\left(M\right) \cdot M^{n + 1} - \operatorname{det}\left(M\right) \cdot M^{n}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/MatrixTracePowerSum.pow_add_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring and every two-by-two matrix, Cayley-Hamilton gives M^(n+2)=trace(M) times M^(n+1) minus det(M) times M^n. This existing recurrence is used by trace_pow_add_two and by the determinant-one Chebyshev transport construction in AndersonDefectFamily.

**Theorem 1.2 (The two-step recurrence for matrix power traces).**

$$\begin{aligned}\forall (R: \operatorname{Type}), [\operatorname{CommRing}\left(R\right)],\\\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), R\right)),\\\forall (n: \mathbb{N}),\\\operatorname{Matrix}.\operatorname{trace}(M^{n + 2}) = \operatorname{Matrix}.\operatorname{trace}(M) \cdot \operatorname{Matrix}.\operatorname{trace}(M^{n + 1}) - \operatorname{Matrix}.\operatorname{det}(M) \cdot \operatorname{Matrix}.\operatorname{trace}(M^{n})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/MatrixTracePowerSum.trace_pow_add_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any commutative ring, the traces of powers of a two-by-two matrix satisfy a two-step recurrence whose coefficients are its trace and determinant.

**Theorem 1.3 (A supplied Vieta pair gives every power trace).**

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

- Truth anchor: `D5/S0/Observation/MatrixTracePowerSum.pow_add_two`
- Truth anchor: `D5/S0/Observation/MatrixTracePowerSum.trace_pow_add_two`
- Truth anchor: `D5/S0/Observation/MatrixTracePowerSum.trace_pow_eq_add_pow`
