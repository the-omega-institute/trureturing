# Profinite Integers Decompose Along the Prime Axes

## Abstract

Compatible residues decompose bijectively into all prime-adic integer coordinates.

**Theorem 1.1 (Compatible residues are equivalent to all prime-adic coordinates).**

$$\widehat{\mathbb{Z}} \sim \prod_{p \text{prime}} \mathbb{Z}_{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ProfinitePrimeDecomposition.profinite_prime_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A compatible residue family assigns a class modulo every positive natural modulus, with reduction along divisibility preserving the assignment. Projecting such a family along the powers of each prime produces one prime-adic integer. The theorem states that the simultaneous projection to every prime is bijective: no compatible residue information is lost, and every family of prime-adic coordinates comes from exactly one compatible residue family.

The pinned Mathlib sources contain the required local ingredients but not this global decomposition theorem. The proof first uses the prime-adic residue maps to construct every projection and their extensionality theorem to compare prime-adic integers. In the reverse direction it applies the finite Chinese remainder equivalence at each modulus, taking the component at a prime to the residue of the supplied prime-adic coordinate at the exact factorization exponent. Reduction compatibility follows from monotonicity of prime exponents under divisibility. The two inverse laws are then proved componentwise, so the result is a new assembly over library declarations rather than a wrapper around an existing equivalence. The source atom contains no numerical certificate.

## References

- Truth anchor: `D5/S3/Factorization/ProfinitePrimeDecomposition.profinite_prime_decomposition`
