# Finite Autocorrelation

## Abstract

A finite Fourier sum has the exact pairwise autocorrelation expansion of its squared modulus.

**Theorem 1.1 (Finite Fourier sums expand into autocorrelation).**

$$\forall N, f, z,\ normSq(finiteSignal(f, z))=finiteAutocorrelation(f, z).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/Interference/FiniteAutocorrelation.finite_autocorrelation_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite complex coefficient sequence and complex frequency, finiteSignal is the corresponding finite power sum and finiteAutocorrelation is its pairwise coefficient-conjugate expansion.

The proof is a direct finite algebra calculation. Mathlib's conjugation homomorphism laws, star_pow, Complex.normSq_eq_conj_mul_self, and finite-sum product and reordering lemmas supply every step; no source instance facts are imported.

This is an honest partial closure of the leading identity clause of the source bundle. The coefficient specialization, diffraction formula, asymptotic peak law, zero-window statement, and corollary remain unresolved.

## References

- Truth anchor: `D5/S0/Asymptotics/Interference/FiniteAutocorrelation.finite_autocorrelation_normSq`
