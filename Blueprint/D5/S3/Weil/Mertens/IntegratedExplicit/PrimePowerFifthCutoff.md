# The sixth-root correction

## Abstract

Chebyshev prime powers through the fifth root

**Theorem 1.1 (The signed sixth-root contribution).**

$$\forall t \in \mathbb{R},\; 2 \le t \Rightarrow \left|\operatorname{R}\left(t\right)+\theta\left(t^{\frac{1}{6}}\right)\right| \le 4 \cdot \operatorname{log}\left(t\right) \cdot t^{\frac{1}{7}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePowerFifthCutoff.abs_psi_sub_roots_add_theta_sixth_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R(t) be ψ(t)−θ(t)−ψ(t^(1/2))−ψ(t^(1/3))−ψ(t^(1/5)).

Use Mathlib's finite Chebyshev decomposition at each root. On a common exponent interval, the sum at the d-th root contains exactly the exponents divisible by d. The coefficient of θ(t^(1/k)) in R(t) is one minus the number of divisors of k among 2, 3 and 5. It vanishes at 2, 3, 4 and 5, and equals −1 at 6.

From exponent seven onward its absolute value is at most two. Chebyshev's linear upper bound for θ gives a bound of log(4) times t^(1/7) per term before multiplying by the coefficient. There are at most log(t)/log(2) terms.

**Theorem 1.2 (A uniform bound for real cutoffs).**

$$\exists C \in \mathbb{R},\; 0 < C \land \left(\forall t \in \mathbb{R},\; 2 \le t \Rightarrow \left|\operatorname{R}\left(t\right)\right| \le C \cdot t^{\frac{1}{6}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePowerFifthCutoff.exists_abs_psi_sub_roots_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inequality log(t) ≤ 42 t^(1/42) brings the tail to sixth-root scale. The triangle inequality and the linear upper bound for θ then give the constant log(4)+168 for every real cutoff t ≥ 2.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePowerFifthCutoff.abs_psi_sub_roots_add_theta_sixth_le`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePowerFifthCutoff.exists_abs_psi_sub_roots_le`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/FifthExponents](PrimePower/FifthExponents.md)
