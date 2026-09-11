# Powerful-Divisor Transform

## Abstract

Powerful-divisor summation is an inverse Moebius transform and preserves multiplicativity.

**Definition 1.1 (Powerful natural numbers).**

$$\operatorname{Powerful}\left(n\right) \equiv n \neq 0 \land \forall p, (\operatorname{Prime}\left(p\right) \land p \mid n) \Rightarrow p^{2} \mid n.$$

*Formalization.* `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.Powerful` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonzero natural number is powerful exactly when the square of every prime dividing it also divides it.

**Definition 1.2 (Characteristic function of powerful numbers).**

$$\operatorname{powerfulIndicator}\left(n\right) = \operatorname{if}(\operatorname{Powerful}\left(n\right), 1, 0).$$

*Formalization.* `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This arithmetic function is the characteristic function A112526.

**Definition 1.3 (Sum over powerful divisors).**

$$\operatorname{powerfulDivisorSum}\left(f, n\right) = \sum_{d \mid n, \operatorname{Powerful}\left(d\right)} \operatorname{f}\left(d\right).$$

*Formalization.* `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulDivisorSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arithmetic function f, the transformed value at n sums f(d) over the powerful divisors d of n.

**Theorem 1.4 (Inverse Moebius transform identity).**

$$\operatorname{powerfulDivisorSum}\left(f\right) = \zeta * (powerfulIndicator \cdot f).$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulDivisorSum_eq_inverseMoebius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The powerful-divisor sum is the Dirichlet convolution of the zeta arithmetic function with the pointwise product of A112526 and f.

**Theorem 1.5 (Preservation of multiplicativity).**

$$\forall f: \operatorname{ArithmeticFunction}\left(\mathbb{N}, R\right), \operatorname{Multiplicative}\left(f\right) \Rightarrow \operatorname{Multiplicative}\left(\operatorname{powerfulDivisorSum}\left(f\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulDivisorSum_isMultiplicative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If f is multiplicative, then its sum over powerful divisors is also multiplicative.

## References

- Truth anchor: `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.Powerful`
- Truth anchor: `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulDivisorSum`
- Truth anchor: `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulDivisorSum_eq_inverseMoebius`
- Truth anchor: `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulDivisorSum_isMultiplicative`
- Truth anchor: `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulIndicator`
