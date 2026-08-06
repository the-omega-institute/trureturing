# Radix Constant Arms

## Abstract

Radix name towers have exact normalized approximation arms at canonical rational points.

At level Q, the radix grid consists of integer multiples of the inverse scale. Its distance is realized by scaling, rounding to a nearest integer, and dividing by the scale.

$$
\operatorname{D}\left(b, Q\right) = \left\{\frac{m}{b^{Q}} \mid m \in \mathbb{Z}\right\}
$$

$$
\operatorname{radixDistance}\left(b, Q, x\right) = \frac{\left|b^{Q} \cdot x - \operatorname{round}\left(b^{Q} \cdot x\right)\right|}{b^{Q}}
$$

**Theorem 1.1 (The reciprocal point has a constant arm).**

$$\forall b \in N, Q \in N,\; \left(b \ge 2 \land Q \ge 1\right) \Rightarrow b^{Q} \cdot \operatorname{radixDistance}\left(b, Q, \frac{1}{b + 1}\right) = \frac{1}{b + 1}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ConstantArms.constant_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every radix b at least two and every level Q at least one, the normalized distance from 1 divided by b plus one to the radix grid is exactly 1 divided by b plus one. The proof uses the power congruence b congruent to minus one modulo b plus one and mathlib's exact nearest integer rounding formula.

**Theorem 1.2 (The even half-radix point has a constant arm).**

$$\forall b \in N, Q \in N,\; \left(\left(b \ge 2 \land Q \ge 1\right) \land \operatorname{Even}\left(b\right)\right) \Rightarrow b^{Q} \cdot \operatorname{radixDistance}\left(b, Q, \frac{\frac{b}{2}}{b + 1}\right) = \frac{b}{2 \cdot \left(b + 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ConstantArms.even_champion_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When b is even, the point b over two times b plus one has normalized distance b over two times b plus one at every positive level. Its two possible residues are the two central residues around half the odd modulus b plus one.

**Theorem 1.3 (Binary one-third is the radix-two specialization).**

$$\forall Q \in N,\; Q \ge 1 \Rightarrow 2^{Q} \cdot \operatorname{radixDistance}\left(2, Q, \frac{1}{3}\right) = \frac{1}{3}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ConstantArms.binary_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binary identity is obtained only by specializing the general reciprocal-point theorem to radix two; it has no independent proof.

## References

- Truth anchor: `D5/S0/Tower/ConstantArms.binary_arm`
- Truth anchor: `D5/S0/Tower/ConstantArms.constant_arm`
- Truth anchor: `D5/S0/Tower/ConstantArms.even_champion_arm`
