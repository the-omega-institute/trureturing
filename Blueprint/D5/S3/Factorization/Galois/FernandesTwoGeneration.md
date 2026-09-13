# Two generators for equal-sign permutation pairs

## Abstract

Two generators for the equal-sign subgroup whenever the second degree is two.

Let Gamma(m,n) be the subgroup of S_m times S_n consisting of pairs whose permutation signs agree. Equivalently, it is the kernel of the ratio of the two signs.

**Theorem 1.1 (Second degree two).**

$$\forall m \in \mathbb{N}, m \geq 2 \Rightarrow \exists g_{1},g_{2} \in \Gamma(m,2), \langle g_{1},g_{2}\rangle = \Gamma(m,2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FernandesTwoGeneration.fernandes_two_generation_n_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sign is injective on S_2, so projection onto S_m is injective on Gamma(m,2). Lift a full cycle and an adjacent transposition to equal-sign pairs. Their projections generate S_m, hence the pairs generate Gamma(m,2).

The two-generator assertion for degree pairs with second degree at least three is not established by this statement.

## References

- Truth anchor: `D5/S3/Factorization/Galois/FernandesTwoGeneration.fernandes_two_generation_n_two`
