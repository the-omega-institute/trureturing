# Shifted Chebyshev Hypergeometric Expansion

## Abstract

The shifted first-kind Chebyshev polynomial has its terminating hypergeometric expansion.

**Theorem 1.1 (Shifted Chebyshev polynomials have explicit Pochhammer coefficients).**

$$\forall n \in \operatorname{Nat}\left(\right), x \in \operatorname{Real}\left(\right),\; \operatorname{ChebyshevT}\left(n, 1 - 2 \cdot x\right) = \sum_{k = 0}^{n} \frac{\operatorname{risingPochhammer}\left(-n, k\right) \cdot \operatorname{risingPochhammer}\left(n, k\right)}{\operatorname{risingPochhammer}\left(\frac{1}{2}, k\right) \cdot \operatorname{factorial}\left(k\right)} \cdot x^{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/ChebyshevHypergeometricExpansion.shifted_chebyshev_hypergeometric_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural degree, evaluating the first-kind Chebyshev polynomial at one minus twice the real input gives the displayed finite sum of rising-Pochhammer coefficients.

This formalizes the self-contained identities (541.4)-(541.5). The earlier analytic notation in the source is not used: R_a is undefined there, and (541.1) reuses nu where later formulas require both a measure nu and a square-scale variable u.

The proof combines polynomial Taylor expansion with Mathlib's recurrence for iterated derivatives of Chebyshev polynomials at one and the rising-Pochhammer successor identity.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevHypergeometricExpansion.shifted_chebyshev_hypergeometric_expansion`
