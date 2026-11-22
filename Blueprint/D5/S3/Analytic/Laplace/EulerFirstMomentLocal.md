# Local continuation of a first-moment transform

## Abstract

The first-moment Euler equation gives a holomorphic extension at a nonzero real cut.

**Theorem 1.1 (Continuation across a nonzero real cut).**

Lean statement: `D5/S3/Analytic/Laplace/EulerFirstMomentLocal.exists_extension_of_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/EulerFirstMomentLocal.exists_extension_of_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c be a nonzero real center and r>0. Suppose P is holomorphic on the complex disk of radius r about c, and L is holomorphic on the right half of that disk, where zL″(z)+3L′(z)=P(z). Then some disk about c with radius δ∈(0,r) admits a holomorphic H agreeing with L on its right half.

If Q is a primitive of z²P(z), then z³L′(z)−Q(z) is constant on the connected right half-disk. Shrink the disk to avoid zero. Dividing Q plus that constant by z³ extends L′, and taking a primitive with the matching additive constant extends L. The construction uses c≠0 to permit this division.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/EulerFirstMomentLocal.exists_extension_of_ne_zero`
- Dependency: [D5/S3/Analytic/Laplace/EulerLocalContinuation](EulerLocalContinuation.md)
