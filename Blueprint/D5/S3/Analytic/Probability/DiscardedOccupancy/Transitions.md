# Transitions of occupancy with discarded throws

## Abstract

A lower bound on early conditional variances gives a linear lower bound for the terminal variance.

**Theorem 1.1 (Variance from the early throws).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), 0<n \implies 0 \leq p \implies p \leq 1 \implies \lfloor \frac{n}{2} \rfloor \cdot \frac{p \cdot (1 - p)^{3}}{2} \leq \operatorname{variance}\left(n, p, n - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here n is the number of ordinary bins and p is the total probability of assigning a throw to an ordinary bin. The trial following x occupied bins increases the count with probability p times one minus x divided by n. The exact weighted variance recursion yields the displayed bound from the first floor of n divided by two increments.

## References

- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_lower`
