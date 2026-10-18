# The interpolation center identity

## Abstract

The trace interpolation function at 1/p equals its prescribed weighted Schur diagonal sum.

**Theorem 1.1 (The trace at the reciprocal exponent).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurStripCenter.center_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurStripCenter.center_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p>0 and let t_j and rho_k be positive. Suppose b_j=u_j t_j, and let mu_k be the diagonal entries of Q* H(n,1/2) diag(b) H(n,1/2) Q. If sum_k conj(v_k) rho_k^(p−1) mu_k=N, then the interpolation trace f(1/p) equals N as a complex number. Trace cyclicity and the identities p(1/p)=1 and p(1−1/p)=p−1 suffice; Q need not be unitary and the conjugated matrix need not be triangular.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurStripCenter.center_identity`
- Dependency: [D5/S3/Zeros/CriticalPoints/SchurStripFunctions](SchurStripFunctions.md)
