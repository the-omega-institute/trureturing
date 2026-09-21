# Merca's Lifted Residue Sum at Prime Order

## Abstract

Merca's lifted residue sum over an even multiplicative-order cycle for a prime modulus.

All variables lie in the natural numbers. The operator mod returns the least non-negative remainder, and the sum includes both endpoints.

**Definition 1.1 (Lifted residue sum).**

$$\forall m \in \mathbb{N}, a \in \mathbb{N},\; liftedSum\left(m, a\right) = \sum_{i = 1}^{orderOf\left(a: ZMod\left(m\right)\right)} mod\left(2 \cdot a^{i} + m, 2 \cdot m\right)$$

*Formalization.* `D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder.liftedSum` (`✓ std3`).

*Citation.* Mircea Merca (2011). *Inequalities and Identities Involving Sums of Integer Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf>.

*Commentary.*

The summand is the least non-negative remainder of the whole quantity 2a^i+m modulo 2m; the parentheses follow formula (39) on the same printed page. The upper bound is Mathlib's multiplicative order of the residue class of a modulo m: the least positive n for which a^n equals one modulo m, and zero if there is no such n. On the claim's prime, coprime domain, a has finite positive order, so the zero convention is not reached.

**Definition 1.2 (Merca's Conjecture 2).**

$$(claim) \Leftrightarrow (\forall a \in \mathbb{N}, m \in \mathbb{N},\; (0 < a) \Rightarrow ((Prime\left(m\right)) \Rightarrow ((Coprime\left(a, m\right)) \Rightarrow ((Even\left(orderOf\left(a: ZMod\left(m\right)\right)\right)) \Rightarrow (liftedSum\left(m, a\right) = m \cdot orderOf\left(a: ZMod\left(m\right)\right))))))$$

*Formalization.* `D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder.claim` (`✓ std3`).

*Citation.* Mircea Merca (2011). *Inequalities and Identities Involving Sums of Integer Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf>.

*Commentary.*

Conjecture 2 states verbatim: Let a and m be relatively prime positive integers. If m is prime and ord_m(a) is even then Σ_{i=1}^{ord_m(a)} (2a^i + m mod 2m) = m · ord_m(a). Here ord_m(a) is represented by Mathlib's orderOf on the residue class of a modulo m, and the displayed mod applies to the whole parenthesized summand; primality supplies positivity of m.

**Theorem 1.3 (Conjecture 2).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mircea Merca (2011). *Inequalities and Identities Involving Sums of Integer Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf>.

*Commentary.*

Write the even order as 2s. In the field modulo m, the s-th power of a squares to one but is not one, so it is minus one. Each residue at i then pairs with the residue at i+s, and the two lifted terms sum to 2m. Summing the s pairs gives m times the full order.

## References

- Truth anchor: `D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder.claim`
- Truth anchor: `D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder.liftedSum`
- Truth anchor: `D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder.result`
