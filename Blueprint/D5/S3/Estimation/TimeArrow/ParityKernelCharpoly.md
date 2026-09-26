# Characteristic Polynomial of Balanced Parity Kernels

## Abstract

A parity kernel on the sign hypercube whose profile a satisfies E a = 0 and E[chi a] = 0 has characteristic polynomial (X - 1) X^(2^d - 1).

**Theorem 1.1 (Characteristic polynomial of a balanced parity kernel).**

$$\sum_{y} \operatorname{a}(y)=0, \sum_{y} \operatorname{chi}(y) \operatorname{a}(y)=0 \Rightarrow \operatorname{charpoly}(P_{a})= (X-1) X^{2^{d}-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityKernelCharpoly.charpoly_parityKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d >= 1 and let a be a real profile on the sign hypercube {-1, 1}^d with sum a = 0 and sum chi a = 0. The kernel matrix P_a(x, y) = (1 + a(x) chi(y)) / 2^d has characteristic polynomial (X - 1) X^(2^d - 1): the eigenvalue 1 is simple and all other eigenvalues vanish with full algebraic multiplicity.

The kernel is the rank-two product U V with U = [1, a] / 2^d, a 2^d by 2 matrix, and V = [1, chi] transposed. The reversed product V U is the 2 by 2 matrix with entries E 1 = 1, E a = 0, E chi = 0 and E[chi a] = 0, that is diag(1, 0). The parity sum E chi = 0 is the instance a = 1, b = 0 of two-step uniform mixing. The Weinstein-Aronszajn identity for characteristic polynomials of rectangular products then gives X^(2^d - 2) (X^2 - X).

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityKernelCharpoly.charpoly_parityKernel`
- Dependency: [D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates](ParityKernelSubcoordinates.md)
