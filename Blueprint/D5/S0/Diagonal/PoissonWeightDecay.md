# Poisson Weight Decay

## Abstract

Fixed finite weights times geometric listing decay tend to zero.

**Theorem 1.1 (The Poisson weight tends to zero).**

$$\forall n,k\in\mathbb{N}, n \ge 2 \land k \le n \Rightarrow \left(\left(\forall A\in\mathbb{N}, 0 \le kAn^{-A} \le An^{1-A} \le A2^{1-A}\right) \land \lim_{A\to\infty} kAn^{-A} = 0 \land \forall \lambda\in\mathbb{R}, \lambda > 0 \Rightarrow \neg\left(\lim_{A\to\infty} kAn^{-A} = \lambda\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/PoissonWeightDecay.poisson_weight_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed natural n at least two and k at most n, the weight is nonnegative and lies below A times n to the one minus A, which in turn lies below A times two to the one minus A. The real sequence tends to zero, and uniqueness of real limits excludes convergence to any positive lambda.

Pinned Mathlib supplies tendsto_self_mul_const_pow_of_lt_one and tendsto_nhds_unique. The Lean declaration is a thin wrapper around that geometric-decay theorem. Elementary ordered-field algebra supplies the source's finite envelope; k at most n is used exactly there.

This is a partial closure of clause (iv) of the source corollary. Clauses (i) and (ii), the separately represented escape-ratio limit in clause (iii), and the dense-phase exclusion in clause (v) remain outside this deposit.

## References

- Truth anchor: `D5/S0/Diagonal/PoissonWeightDecay.poisson_weight_tendsto_zero`
