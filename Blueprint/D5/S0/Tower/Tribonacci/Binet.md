# Tribonacci Binet Coefficient

## Abstract

The Tribonacci recurrence has an exact Perron coefficient and bounded secondary roots.

**Definition 1.1 (Exact Perron coefficient).**

$$a = \frac{t^{2}}{t^{2} + 2 \cdot t + 3}$$

*Formalization.* `D5/S0/Tower/Tribonacci/Binet.tribonacciBinetCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial values zero, one, one select t squared divided by t squared plus two t plus three as the coefficient of t to the n.

**Theorem 1.2 (The exact Binet remainder tends to zero).**

$$\operatorname{limitAtTop}\left(\left(\operatorname{T}\left(n\right) - a \cdot t^{n}\right)_{n \in N}\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Binet.tribonacci_binet_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the residual quadratic factor isolates the Perron mode. The remaining term is an exact fixed linear combination of two consecutive frozen Perron errors, so it converges to zero.

**Theorem 1.3 (Secondary roots lie inside the unit disk).**

$$\forall z \in C,\; \left(z^{3} = z^{2} + z + 1 \land z \ne t\right) \Rightarrow \operatorname{abs}\left(z\right) < 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Binet.abs_lt_one_of_tribonacci_root_ne_perron` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the Perron factor leaves a real quadratic. Its negative discriminant forces each secondary root to be nonreal, while its real and imaginary equations give squared modulus t inverse, which is strictly below one.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/Binet.abs_lt_one_of_tribonacci_root_ne_perron`
- Truth anchor: `D5/S0/Tower/Tribonacci/Binet.tribonacciBinetCoefficient`
- Truth anchor: `D5/S0/Tower/Tribonacci/Binet.tribonacci_binet_tendsto_zero`
- Dependency: [D5/S0/Tower/Tribonacci/PerronRoot](PerronRoot.md)
