# Norm-One Trace and Companion Doubling Identities

## Abstract

A pair whose product is one satisfies trace and discriminant-weighted companion doubling identities in a commutative ring.

**Theorem 1.1 (Square of the trace expression).**

$$\begin{gathered}\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall a, b: R,\\{a \cdot b = 1} \implies\\\forall n: \mathbb{N},\\{{a}^{n} + {b}^{n}}^{2} = {{a}^{2 \cdot n} + {b}^{2 \cdot n}} + 2.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/NormOneLucasDouble.trace_sq_eq_trace_two_mul_add_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cross term is a^n * b^n = (a * b)^n = 1. Expanding the square and rewriting each square of an n-th power at index 2 * n therefore leaves the doubled-index sum plus two.

All Lucas results frozen in this repository concern the specific golden-ratio instance, whose discriminant is five; this module proves the general form for an arbitrary norm-one conjugate pair and makes no new assertion about that existing instance.

**Theorem 1.2 (Weighted square of the companion expression).**

$$\begin{gathered}\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall a, b, u: R,\\{a \cdot b = 1} \implies\\\forall n: \mathbb{N},\\{{a - b} \cdot u = {a}^{n} - {b}^{n}} \implies\\{a - b}^{2} \cdot {u}^{2} = {{a}^{2 \cdot n} + {b}^{2 \cdot n}} - 2.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/NormOneLucasDouble.companion_sq_eq_trace_two_mul_sub_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Again, the cross term reduces through a^n * b^n = (a * b)^n = 1. Squaring the entire equation (a - b) * u = a^n - b^n and substituting it into the expanded square gives the doubled-index sum minus two.

The argument uses only commutative-ring identities and the two stated equations; it makes no classification or arithmetic claim beyond the displayed identity.

## References

- Truth anchor: `D5/S1/Recurrence/NormOneLucasDouble.companion_sq_eq_trace_two_mul_sub_two`
- Truth anchor: `D5/S1/Recurrence/NormOneLucasDouble.trace_sq_eq_trace_two_mul_add_two`
