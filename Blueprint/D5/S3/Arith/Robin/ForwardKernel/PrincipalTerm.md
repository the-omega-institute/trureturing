# The signed principal Mellin kernel

## Abstract

The triangular principal coefficient gives the complete Mangoldt logarithmic derivative.

**Theorem 1.1 (The complete signed principal limit).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrincipalTerm.principal_signed_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrincipalTerm.principal_signed_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re(s)>1/2, take the sum of Lambda(n)*n^(-s-1/2)/2 over 0<=n<=floor(b), and subtract the integral of t^(-s-1/2)/2 from 1 to b. Its limit as b tends to infinity is -zeta'(s+1/2)/(2*zeta(s+1/2))-1/(2*(s-1/2)). Mathlib supplies absolute summability of the full von Mangoldt Dirichlet series and its equality with the negative logarithmic derivative. The ordinary complex-power integral supplies the subtracted density. All prime powers retain their full weights.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrincipalTerm.principal_signed_tendsto`
