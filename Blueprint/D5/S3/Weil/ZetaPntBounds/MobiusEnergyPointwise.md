# Persistence of the reciprocal-weighted prefix

## Abstract

Pointwise Möbius bounds from weighted energy

**Theorem 1.1 (Ordinary Möbius prefixes under a zero-free half-plane).**

$$\forall t \in \mathbb{R},\; \forall a \in \mathbb{R},\; \left(\left(\frac{1}{2} \le t \land t < 1\right) \land \left(\operatorname{Z}\left(t\right) \land \left(2 \cdot t - 1 < a \land a < 1\right)\right)\right) \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall N \in \mathbb{N},\; 1 \le N \Rightarrow \left|\operatorname{M}\left(N\right)\right| \le C \cdot N^{\frac{2 + a}{3}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusEnergyPointwise.unweighted_mobius_prefix_power_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-free condition Z(t) means ζ(z)≠0 for every complex z with Re(z)>t and z≠1. M(N) is the ordinary unweighted finite sum of the Möbius function over integers from 1 to N.

Let S(x) be the sum of μ(n)/n over integers 1≤n≤x. At an integer N, every subsequent change has size at most 1/N. A height H=|S(N)| therefore forces magnitude at least H/2 throughout the real interval from N to N+HN/2. This covers intervals shorter than one integer step.

Compare the energy on that interval to the finite integral of S(x)² x^(−α) on x>1. This bounds H³N^(1−α) by the energy times a constant. Discrete partial summation gives M(N)=NS(N)−Σ S(k) over 1≤k<N. Comparing the resulting decreasing power sum with its integral gives the exponent (2+α)/3.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusEnergyPointwise.unweighted_mobius_prefix_power_bound`
