# Classifying the smallest nonzero integral Huang residuals

## Abstract

Integral Q9 vectors of squared norm nine whose Huang image is divisible by three have two explicit forms.

This classification serves the structural study of candidates for Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2). The original f₂(Q₉)=3-or-4 question remains unresolved by this statement. No claim of literature novelty or full lattice classification is made.

**Theorem 1.1 (Only a signed triple coordinate vector or a signed Huang column).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangMinimalResidual.classify_nine_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangMinimalResidual.classify_nine_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary integer vector r on actual Q9, assume the sum of its squared coordinates is nine and every coordinate of intA r is divisible by three. Here intA and intCoeff are the original integer Huang operator and coefficients from HuangIntegralNormGap; their real casts equal the original FALSE-prefix Huang matrix. Then r is either ±3 times a coordinate vector or ± one integer column of that same matrix. No support classification or common-neighbor bound is supplied as an extra hypothesis.

The squared norm bounds the nonempty support by nine. A singleton neighbor forces its selected coefficient to be a nonzero multiple of three, using the entire squared norm. Otherwise CubeNineSupport identifies the support as a full nine-point neighborhood, with all coefficients equal to ±1. Away from its center, a row of intA has at most two nonzero unit contributions. Divisibility by three makes each such row zero. Thus intA r is supported only at the center, and the existing identity intA² = 9I recovers the signed matrix column.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangMinimalResidual.classify_nine_residual`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubeNineSupport](CubeNineSupport.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport](CubeSmallSupport.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangIntegralNormGap](HuangIntegralNormGap.md)
