# Disjoint Strict-Suffix Energy

## Abstract

Distinct prefix-free stopping addresses have disjoint strict-descendant coordinates in the original increment space. Their suffix energies therefore fit inside the original energy.

**Theorem 1.1 (Disjoint Original Edge Coordinates).**

$$\forall A: \operatorname{Finset}\left(\operatorname{Address}\left(\right)\right), (\forall z: \operatorname{H}\left(\right), (\operatorname{IsPrefixFree}\left(A\right)\implies \sum_{p\in A} ((\Vert \operatorname{S}\left(p, z\right)\Vert)^{2})\leq (\Vert z\Vert)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffixEnergy.prefix_free_suffix_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be any finite prefix-free set of original addresses and let z be any vector in the original square-summable edge space H. Then the sum over A of the squared norms of S(p)z is at most the squared norm of z. Nonempty suffixes are used throughout, so the edge ending at p is excluded.

The map sending a pair consisting of p in A and a nonempty suffix u to the original edge pu is injective. If two such edges agreed, their prefixes would be comparable; prefix freedom would force the prefixes to agree, and cancellation would force the suffixes to agree. The resulting subseries of the nonnegative squared edge coordinates is bounded by the complete energy series. This argument applies directly to every z in H.

**Theorem 1.2 (Weighted Actual Centered Suffixes).**

$$\forall A: \operatorname{Finset}\left(\operatorname{Address}\left(\right)\right), (\forall w: \operatorname{Address}\left(\right)\to \operatorname{Real}\left(\right), (\forall t: \operatorname{Real}\left(\right), (\forall z: \operatorname{H}\left(\right), (0\leq t\land \operatorname{IsPrefixFree}\left(A\right)\land (\forall p\in A, 0\leq \operatorname{w}\left(p\right)\leq t)\implies \sum_{p\in A} (\operatorname{w}\left(p\right)\cdot (\Vert \operatorname{C}\left(\operatorname{S}\left(p, z\right)\right)\Vert)^{2})\leq \operatorname{goldenRatio}\left(\right)\cdot t\cdot (\Vert z\Vert)^{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffixEnergy.weighted_centered_suffix_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose t is nonnegative and each weight w(p), for p in A, lies between zero and t. For the actual centered trace C on the original biased boundary, the sum of w(p) times the squared norm of C(S(p)z) is at most the golden ratio times t times the squared norm of z.

Apply the actual conditional centering identity and its Hardy estimate to each suffix, use w(p) at most t, and then apply the disjoint strict-suffix energy estimate. The weights can be actual cylinder masses whenever their threshold bound has been established.

This estimate supplies the suffix-energy inequalities in a stopping argument. Identifying this weighted sum with the norm of the global atom-average residual requires the actual cylinder projection and its conditional norm decomposition. No assertion about the covariance or the spectral counting function follows here alone.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffixEnergy.prefix_free_suffix_energy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffixEnergy.weighted_centered_suffix_energy`
- Dependency: [D5/S0/Computability/Coding/BiasedMassFrontier](../../../../S0/Computability/Coding/BiasedMassFrontier.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering](BiasedBoundaryCentering.md)
