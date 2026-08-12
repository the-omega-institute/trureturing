# A Heat-Entropy Lower Bound

## Abstract

A nonnegative information-and-divergence remainder turns an exact heat-entropy balance into a lower bound.

**Theorem 1.1 (Discarding nonnegative remainders gives the lower bound).**

$$\forall beta, heat, entropyChange, mutualInfo, divergence \in \mathbb{R},\ beta \cdot heat = -entropyChange + mutualInfo + divergence \land 0 \le mutualInfo \land 0 \le divergence \Rightarrow -entropyChange \le beta\cdot heat$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LandauerBound.landauer_bound_of_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let beta times the heat be exactly the negative entropy change plus a mutual-information remainder and a divergence remainder. When both remainders are nonnegative, their sum can be discarded, leaving the negative entropy change bounded above by beta times the heat.

The balance identity and the two nonnegativity statements are explicit hypotheses. This result does not derive that physical balance law; it isolates the order-theoretic step from the balance to the lower bound.

## References

- Truth anchor: `D5/S3/DivergenceSupport/LandauerBound.landauer_bound_of_balance`
