# Cyclotomic Factorization of a Geometric Sum

## Abstract

A finite geometric sum factors into the cyclotomic polynomials indexed by its nontrivial divisors.

**Theorem 1.1 (The geometric sum is the product of its nontrivial cyclotomic factors).**

$$\forall R, [\operatorname{CommRing}(R)],\ \forall n \in \mathbb{N}, n>0 \Rightarrow \sum_{i=0}^{n-1} X^i = \prod_{d \mid n, d>1} \phi_d(X)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Cyclotomic/GeometricSpectrumFactorization.geometric_sum_eq_cyclotomic_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring R and positive natural number n, the polynomial with one monomial in each degree from zero through n minus one equals the product of the d-th cyclotomic polynomials over all divisors d of n other than one.

Pinned Mathlib was searched before proof construction and contains this exact identity as Polynomial.prod_cyclotomic_eq_geom_sum. The Lean declaration only reverses that equality to match the source orientation; it does not reconstruct the cyclotomic factorization.

This closes only the opening factorization identity in remark 27.589, clause 2. The coefficient-sign classification, the claimed uniqueness criterion for prime powers, the alternative composite decompositions, and the finite numerical census remain outside this declaration.

## References

- Truth anchor: `D5/S3/Factorization/Cyclotomic/GeometricSpectrumFactorization.geometric_sum_eq_cyclotomic_product`
