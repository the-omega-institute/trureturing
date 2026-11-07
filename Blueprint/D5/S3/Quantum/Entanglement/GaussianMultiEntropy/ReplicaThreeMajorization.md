# Strict Schur comparison of positive scalar triples

## Abstract

On each positive-real fixed-sum plane the order-three scalar expression is strictly Schur-convex. Among comparable triples equality occurs exactly for permutations. This does not assert that incomparable triples have different values, or that real scalar sizes are physical fractional modes.

The finite balancing law is from Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0. The majorization criterion is classical (Marshall, Olkin and Arnold); the physical family is due to Camargo and Nishida. The existing PositiveSimplexGeometryAndMixing and LogScalarCurvatureMonotone modules supply the positive T-transform chain, and retain their existing authorship.

**Theorem 1.1 (Majorization, strictness and permutation equality).**

$$V(k,x)\le V(k,y);V(k,x)=V(k,y) \iff \exists \sigma\in Perm(\{0,1,2\}),x=y\circ \sigma$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeMajorization.schur_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k > 0 and positive real triples x and y, suppose x is more mixed than y in the standard descending-prefix-sum majorization order. This includes equality of their total sums. Then V(k,x) <= V(k,y), and equality holds if and only if x is a permutation of y. Hence non-permutation majorization gives a strict inequality. The proof normalizes the common positive sum to one and rescales k to preserve the scalar expression. The existing positive T-transform chain then reduces comparison to the proved strict pair-mixing law. Every intermediate triple stays positive; equality along the chain can contain only identity, full-swap or tied-pair steps and therefore yields a permutation. No Schur property is a hypothesis.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeMajorization.schur_comparison`
- Dependency: [D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone](../../../Geometry/AlphaGeometry/LogScalarCurvatureMonotone.md)
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeBalancing](ReplicaThreeBalancing.md)
