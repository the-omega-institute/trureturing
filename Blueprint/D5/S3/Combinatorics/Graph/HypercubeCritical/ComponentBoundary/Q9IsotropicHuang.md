# Weighted coordinate flips and supported codewords

## Abstract

Prime-field specialization of the weighted Huang action

**Theorem 1.1 (A nonzero supported weighted eigenvector gives a word on one parity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang.exists_one_parity_word`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang.exists_one_parity_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integer weights on the signed coordinate flips give an integer matrix whose action over the reals is the corresponding weighted Huang operator. Each flip changes Hamming parity.

If the integer eigenvalue is divisible by a prime, specialization gives a nonzero modular kernel vector supported within the prescribed set. Splitting by Hamming parity leaves at least one nonzero summand in the kernel.

This gives a necessary arithmetic test for the separated components in Hong, Wu and Xia's 258-vertex problem in the nine-cube. The weighted action can be tested over finite fields using exact row reduction on the two parity column restrictions.

**Theorem 1.2 (Parity exactness over a field at nonzero isotropic weights).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang.weightedAction_parity_image_eq_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang.weightedAction_parity_image_eq_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Project onto the bit-true slice for a fixed coordinate and apply its signed flip. The anticommutator of this half flip with the weighted action is the scalar weight in that coordinate.

At an isotropic weight vector over a field, the weighted action squares to zero. A nonzero coordinate weight makes the half flip a contraction. Both maps exchange parity, so the image on each parity is the kernel on the other. The argument also applies in characteristic two.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang.exists_one_parity_word`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang.weightedAction_parity_image_eq_kernel`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicSupport](Q9IsotropicSupport.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangIntegralNormGap](../HuangIntegralNormGap.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointEightWord](../TwentyPointEightWord.md)
