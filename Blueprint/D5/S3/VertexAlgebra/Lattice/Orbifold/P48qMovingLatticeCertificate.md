# The P48q Integral Moving Lattice

## Abstract

For the order-three row action in the Nebe–Sloane P48q catalogue basis, the integral norm kernel equals the integral difference image.

**Theorem 1.1 (The integral norm kernel equals the integral difference image).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qMovingLatticeCertificate.nebeOrderThree_moving_exact`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qMovingLatticeCertificate.nebeOrderThree_moving_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

Let A be the fourth power of the first generator in the Nebe–Sloane catalogue’s P48q entry, acting on rows by right multiplication. Write I for the identity matrix, N = I + A + A² for the cyclic norm, and B = I − A. For every row x indexed by Fin 48 with integer entries, xN = 0 if and only if there is a row y with the same index set and integer entries such that yB = x.

The kernel checks the entries of the integral matrix identity I = UB + NV + 3E, where U, V and E are the certificate matrices. The cube identity A³ = I gives BN = 0, so every row of the form yB is in the norm kernel.

If xN = 0, the certificate gives x = (xU)B + 3(xE). Multiplying this identity by N and cancelling 3 in each integer coordinate gives (xE)N = 0. Because (2I + A)B = 3I − N, the integral row y = xU + (xE)(2I + A) satisfies yB = x.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qMovingLatticeCertificate.nebeOrderThree_moving_exact`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate](P48qFixedRankCertificate.md)
