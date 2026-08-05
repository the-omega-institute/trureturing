# Golden Discriminant

## Abstract

The golden polynomial has discriminant five and the golden ratio satisfies it.

**Theorem 1.1 (Discriminant and fixed-point identity).**

$${-1}^2 - 4 \times 1 \times {-1} = 5 \land \varphi^2 = \varphi + 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/GoldenDiscriminant.golden_discriminant_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct computes the discriminant of x squared minus x minus one from its integer coefficients. The second conjunct reuses the frozen golden-ratio specification.
