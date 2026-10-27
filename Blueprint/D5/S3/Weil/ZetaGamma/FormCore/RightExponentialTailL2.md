# The literal right tail on arbitrary half-line L2 inputs

## Abstract

Actual exponential-tail integration and a pointwise L2 estimate with the exact kernel norm.

**Theorem 1.1 (Actual Bochner integrability and the translated tail mass).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL2.right_exponential_tail_l2_integrable_and_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL2.right_exponential_tail_l2_integrable_and_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k>0 and any complex profile in L2 on the positive half-line, the literal integral R_k u(t)=integral(exp(-k*s)*u(t+s),s>0) is Bochner integrable at every t>=0. Its squared magnitude is at most integral(|u(x)|^2,x>t)/(2*k). No continuity or compact support of the input is assumed.

The proof translates the half-line L2 input by using its zero extension for membership. The exponential kernel has squared L2 norm exactly 1/(2*k); Holder at exponent 2 proves product integrability and the bound. The estimate keeps the actual translated tail mass rather than replacing it with a formal operator norm or an abstract extension.

This estimate supplies actual pointwise and endpoint control for weighted completion arguments. It does not itself establish a complete weighted energy identity, the arithmetic debit, or the positivity required for RH.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL2.right_exponential_tail_l2_integrable_and_sq_le`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail](RightExponentialTail.md)
