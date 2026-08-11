# The Hidden Fiber of the Universal Solenoid

## Abstract

The universal solenoid projects exactly onto the circle with all-prime profinite kernel.

**Theorem 1.1 (The visible circle projection has the all-prime profinite kernel).**

$$0 \to \prod_{p \text{prime}} \mathbb{Z}_{p} \to \Sigma \to \mathbb{T} \to 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/SolenoidProfiniteKernel.universal_solenoid_profinite_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal solenoid is the compatible family of circle phases indexed by all positive moduli. Evaluation at modulus one is surjective onto the visible circle. The theorem proves exactness at the solenoid and identifies the full kernel bijectively with one prime-adic integer coordinate for every prime. Thus every kernel point is present in the displayed product exactly once.

This is new assembly over pinned Mathlib rather than a wrapper around an existing solenoid theorem. A compatible residue modulo each positive integer maps to a compatible circle coordinate. Conversely, a kernel point has an m-torsion coordinate at every modulus m; the finite-torsion classification of the circle recovers its unique residue. Compatibility follows from the solenoid relation and injectivity of the residue embedding into the circle. The resulting residue equivalence is composed with the deposited prime-adic decomposition. The source atom contains no numerical certificate.

## References

- Truth anchor: `D5/S3/Factorization/SolenoidProfiniteKernel.universal_solenoid_profinite_exact`
- Dependency: [D5/S1/Dynamics/UniversalSolenoid](../../S1/Dynamics/UniversalSolenoid.md)
- Dependency: [D5/S3/Factorization/ProfinitePrimeDecomposition](ProfinitePrimeDecomposition.md)
