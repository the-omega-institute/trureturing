# Tribonacci Irrationality

## Abstract

The Tribonacci constant is irrational.

The constant satisfies a monic cubic with integer coefficients, so a rational equal to it would have denominator dividing the cube of its numerator; being in lowest terms, that denominator is one and the constant would be an integer. It lies strictly between one and two, where there is no integer.

All three inputs were already in the tree: the defining cubic and the two bounds. What was absent was this conclusion. The quadratic base of the non-Pisot frontier has its irrationality; the cubic constant, which is older and more central, did not.

**Theorem 1.1 (The Tribonacci constant is irrational).**

$$\operatorname{Irrational}\left(\mathit{tribonacciConstant}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciIrrationality.tribonacciConstant_irrational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinned Mathlib's irrationality lemma for n-th roots does not apply to a general cubic, so the argument is elementary rather than imported. The rational-root step uses the coprimality of numerator and denominator directly.

## References

- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciIrrationality.tribonacciConstant_irrational`
- Dependency: [D5/S0/Tower/Tribonacci/Values](../../../S0/Tower/Tribonacci/Values.md)
