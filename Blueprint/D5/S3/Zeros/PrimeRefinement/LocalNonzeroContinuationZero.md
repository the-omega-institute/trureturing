# Local Nonzero Factors and a Continued Zeta Zero

## Abstract

Prime Euler factors can stay nonzero at a zero of analytically continued zeta.

**Definition 1.1 (Every prime Euler factor is nonzero at a parameter).**

Lean statement: `D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.EveryPrimeEulerFactorNonzeroAt`

*Formalization.* `D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.EveryPrimeEulerFactorNonzeroAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This predicate records pointwise nonvanishing of each prime-indexed inverse Euler denominator. It asserts no convergence of the corresponding infinite product.

**Theorem 1.2 (Base one is the only local obstruction at minus two).**

$$\forall p \in \mathbb{N}, p \neq 1 \Rightarrow (1 - p^{2})^{-1} \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.local_euler_factor_ne_zero_of_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At minus two, every natural base other than one has a nonzero local inverse denominator. The proof therefore weakens primality to its exact algebraic requirement for this witness.

**Theorem 1.3 (Excluding base one is necessary).**

$$(\operatorname{finiteEulerDenominator}(1, -2))^{-1} = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.base_one_exclusion_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete base-one factor is zero at minus two. Thus extending the local claim to every natural base without an exclusion is false.

**Theorem 1.4 (Local nonzero does not force continuation nonzero).**

$$\exists s \in \mathbb{C}, \operatorname{EveryPrimeEulerFactorNonzeroAt}(s) \land (\forall S \subset_{\mathrm{fin}} \mathbb{N}, (\forall p \in S, \operatorname{Prime}(p)) \Rightarrow \operatorname{finiteEulerProduct}(S, s) \neq 0) \land \zeta(s) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.local_euler_nonzero_continuation_zero_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness is minus two. Every prime local factor and every finite prime window is nonzero there, while the analytically continued Riemann zeta function vanishes by its first trivial-zero theorem. No infinite Euler-product convergence at minus two is claimed.

## References

- Truth anchor: `D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.EveryPrimeEulerFactorNonzeroAt`
- Truth anchor: `D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.base_one_exclusion_is_necessary`
- Truth anchor: `D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.local_euler_factor_ne_zero_of_ne_one`
- Truth anchor: `D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.local_euler_nonzero_continuation_zero_counterexample`
- Dependency: [D5/S3/Weil/EulerProduct](../../Weil/EulerProduct.md)
