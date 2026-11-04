# Backward propagation of polynomial values

## Abstract

Additive subgroup membership of rational polynomial values extends from natural inputs to all integer inputs.

**Theorem 1.1 (Natural inputs determine subgroup membership at negative integers).**

Lean statement: `D5/S3/Arith/PolynomialValues/BackwardPropagation.eval_int_mem_of_eval_nat_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PolynomialValues/BackwardPropagation.eval_int_mem_of_eval_nat_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let H be any additive subgroup of the rational numbers and p a rational polynomial. If p(m) lies in H for every natural number m, then p(z) lies in H for every integer z. The subgroup need not be closed under multiplication or division. In particular, taking H to be the image of the integers in the rationals proves integer-valuedness at negative inputs from integer-valuedness at all nonnegative inputs.

The forward difference of order d=degree(p)+1 vanishes. At an integer x, its expansion is a linear relation among p(x),...,p(x+d) with integer coefficients, and the coefficient of p(x) is (-1)^d. Suppose all evaluations at integers greater than x already lie in H. Every term other than p(x) belongs to H, so the relation puts (-1)^d p(x) in H. Multiplication by the same sign recovers p(x). Induction towards negative integers proves the assertion. The vanishing forward-difference identity is supplied by Mathlib; the backward subgroup propagation supplies the extension.

For a residue polynomial of shifted metallic Hankel determinants, equality with integral determinants at every m>=0 supplies the hypothesis for H equal to the integer image. The theorem then supplies values at all negative integers. It neither constructs the residue polynomial nor proves that any shifted determinant has a polynomial formula. Those are separate conditions.

## References

- Truth anchor: `D5/S3/Arith/PolynomialValues/BackwardPropagation.eval_int_mem_of_eval_nat_mem`
