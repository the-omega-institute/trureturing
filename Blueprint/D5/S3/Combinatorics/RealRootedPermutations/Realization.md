# Realizing Unimodal Coefficient Permutations

## Abstract

Integer exponent heights realize every unimodal coefficient ordering strictly.

**Theorem 1.1 (A product of integer powers).**

$$\forall I \in \operatorname{Type},\; \forall S \in \operatorname{Finset}\left(I\right),\; \forall b \in I \to \mathbb{Z},\; \forall T \in \mathbb{R},\; T \ne 0 \Rightarrow \prod_{i\in S} T^{b\left(i\right)} = T^{\sum_{i\in S} b\left(i\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RealRootedPermutations/Realization.product_zpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero real base, multiplying integer powers over a finite set adds their exponents. This identity combines the individual site factors in the reciprocal-weight calculation.

**Theorem 1.2 (Every unimodal permutation has a strict realization).**

Lean statement: `D5/S3/Combinatorics/RealRootedPermutations/Realization.realize_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RealRootedPermutations/Realization.realize_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every unimodal permutation of Fin(n+1), there are n+1 strictly positive real numbers r(i) such that the nonconstant coefficients of the product of 1+r(i)x strictly increase in the specified permutation order. Permutation value v denotes coefficient index v+1; the constant coefficient is omitted.

Write N=n+1 and let rho be the inverse permutation. Assign A(v)=2^(n-rho(v)), H(0)=0 and H(v+1)=2^N-A(v). The integer increments b(i)=H(i+1)-H(i) strictly decrease: before the peak, the preceding weight is at least twice the current weight; after the peak, the following weight is at least twice the current weight. The first increment is treated using A(0) at most 2^n.

Choose T=2^N+1 and r(i)=T^b(i), with integer powers. Finset.prod_one_add expands the polynomial, and coefficient extraction retains exactly the subsets of cardinality k. Since b is decreasing, the first k indices maximize the exponent sum. To compare any subset with this initial segment, Finset.orderEmbOfFin lists its elements increasingly; its j-th element is at least j. Summing the increments on the initial segment telescopes to H(k).

Each subset product is positive and at most T^H(k), while the initial segment contributes exactly T^H(k). There are at most 2^N subsets, so T^H(k) is at most the k-th coefficient and that coefficient is at most 2^N times T^H(k). Increasing inverse positions increase the integer heights by at least one. Since 2^N is strictly less than T, the upper bound at one height is strictly below the lower bound at the next height. These inequalities prove the required strict sorting, including the one-factor case.

## References

- Truth anchor: `D5/S3/Combinatorics/RealRootedPermutations/Realization.product_zpow`
- Truth anchor: `D5/S3/Combinatorics/RealRootedPermutations/Realization.realize_strict`
- Dependency: [D5/S3/Combinatorics/RealRootedPermutations/Defs](Defs.md)
