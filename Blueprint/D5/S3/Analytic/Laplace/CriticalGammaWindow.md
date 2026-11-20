# Concentration at a fixed multiplicative width

## Abstract

Concentration of normalized Laplace moments outside a critical window

**Theorem 1.1 (An explicit moment order controls both tails).**

$$\forall a \in \mathbb{R},\; 1 \le a \Rightarrow \left(\forall g \in \mathbb{R} \to \mathbb{R},\; \operatorname{Measurable}\left(g\right) \Rightarrow \left(\forall M \in \mathbb{R},\; \left(\forall u \in \mathbb{R},\; 0 \le u \Rightarrow \left|g\left(u\right)\right| \le M \cdot \operatorname{exp}\left(2 \cdot u\right)\right) \Rightarrow \left(a \le k \land \left(\operatorname{IntegrableOn}\left(f, S\right) \land \int_{S} f\left(u\right) du \le M \cdot \left(\frac{1}{542} + \frac{1}{478}\right) \cdot 512^{-k}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CriticalGammaWindow.critical_window_off_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real cutoff a ≥ 1 set k = floor(640a). Let S be the part of the positive half-line outside the closed interval [a,3a/2], and write f(u) = |g(u)| uᵏ exp(−512u)/k!. The same k works for every real measurable function g bounded in absolute value by M exp(2u) for u ≥ 0.

After the growth bound, the remaining damping rate is 510. On the left tail use rate 542 with multiplier exp(32a). On the right use rate 478 with multiplier exp(−48a). Extending each positive majorant to the whole positive half-line gives r to the power −(k+1) by the Gamma integral.

The inequalities 640a−1 ≤ k ≤ 640a and the elementary logarithmic bounds absorb the two multipliers. The left and right contributions are at most M times 512 to the power −k divided by 542 and 478 respectively.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/CriticalGammaWindow.critical_window_off_mass`
