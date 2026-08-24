# Finite Prime Extraction Zero Persistence

## Abstract

A critical-strip zeta zero persists after any finite extraction of prime Euler factors.

**Theorem 1.1 (Finite prime extraction preserves a zeta zero).**

$$\forall \rho \in \mathbb{C}, \forall S \subset_{\mathrm{fin}} \mathbb{N}, (0 < \Re(\rho) \land \Re(\rho) < 1 \land \zeta(\rho) = 0 \land \forall p \in S, \operatorname{Prime}(p)) \Rightarrow \zeta(\rho) \cdot \prod_{p \in S} (1 - (p)^{-\rho}) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PrimeRefinement/FinitePrimeExtractionZeroPersistence.finite_prime_extraction_preserves_zeta_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public statement constructs the analytic residual directly as zeta at rho multiplied by the finite product of local factors. The finite set, the primality of each member, both open-strip bounds, and the zeta-zero hypothesis are all explicit.

The proof applies the frozen finite-prime-modification zero-set theorem. Unfolding that repository modification and its finite Euler product turns division by the product of inverse denominators into the displayed product of denominators.

## References

- Truth anchor: `D5/S3/Zeros/PrimeRefinement/FinitePrimeExtractionZeroPersistence.finite_prime_extraction_preserves_zeta_zero`
- Dependency: [D5/S3/Weil/PrimeAddress/PrimeAddress](../../Weil/PrimeAddress/PrimeAddress.md)
