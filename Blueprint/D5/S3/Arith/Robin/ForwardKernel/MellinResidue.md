# The generalized Mellin identity

## Abstract

The generalized Mellin identity.

**Theorem 1.1 (The generalized Mellin identity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MellinResidue.forward_kernel_mellin_residue`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MellinResidue.forward_kernel_mellin_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha>=0 and assume there are real C and t0 with |psi(t)-t|<=C*t^alpha for every t>=t0. For each x0>=3, the Mellin integral F(s) of the original complete forward response has a remainder R holomorphic on Re(s)>alpha-7/10. On the overlap Re(s)>max(1/2,alpha-3/10), F(s)=-zeta'(s+1/2)/(2*zeta(s+1/2))-1/(2*(s-1/2))+R(s). Absolute Fubini gives the signed adjoint. Its principal term is t^(-s-1/2)/2, and its remainder and time derivative gain t^(-1/5). Partial summation gives the integral of the error against that derivative. The finite initial correction is entire. The original Mellin integral converges absolutely for Re(s)>alpha-3/10.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MellinResidue.forward_kernel_mellin_residue`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FiniteMellin](FiniteMellin.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Fubini](Fubini.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/InverseTransport](InverseTransport.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrincipalTerm](PrincipalTerm.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/SignedRemainder](SignedRemainder.md)
