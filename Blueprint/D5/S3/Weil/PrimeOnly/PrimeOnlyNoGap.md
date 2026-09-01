# Prime-Only No-Gap Theorem

## Abstract

The prime-only jump Laplacian has nonnegative nonzero-mode energies whose infimum vanishes throughout the absolutely convergent half-plane.

**Theorem 1.1 (Prime-only spectral coefficients have no positive uniform gap).**

$$sigma > 1 \Rightarrow \operatorname{inf}\left(\{n\in Z \mid n \neq 0\}, C_{n}\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeOnly/PrimeOnlyNoGap.numberField_prime_only_no_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The jump indices are positive powers of genuine prime ideals in a number field. Dedekind-zeta convergence for sigma greater than one makes their weights summable.

Compact recurrence in every finite product of regulator circles gives a nonzero integer mode simultaneously close to the identity for any finite collection of prime-power shifts. No irrationality premise on the shifts is needed.

A finite-tail split then makes the Fourier jump energy arbitrarily small. Nonnegativity supplies the reverse bound, so the infimum over the subtype of nonzero integer modes is exactly zero.

## References

- Truth anchor: `D5/S3/Weil/PrimeOnly/PrimeOnlyNoGap.numberField_prime_only_no_gap`
