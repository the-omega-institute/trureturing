# Coefficient recovery and support

## Abstract

The coefficients recover the full parameter tuple and enforce the two support cuts.

**Definition 1.1 (Parameter space).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.Params`

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.Params` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For intermediate fields K and L of E over F, the parameter space is L⁴ × K. The entries are embedded in E when used as coefficients.

**Definition 1.2 (Linear coefficient map).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients`

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Over a finite base field F of order q, put δ = b^(q³) − b for b in E. At parameters (u,a₁,a₂,ℓ,k), the map takes a₃ = δ⁻¹(ℓ + ck − bu) and returns (u − a₃,a₁,a₂,a₃). The map is defined for all b and c in E.

**Theorem 1.3 (Recovery of the five parameters).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K ≤ L be intermediate fields of E over the finite field F. If β is a four-vector K-basis of E whose first two vectors span L over K, and δ is nonzero, the coefficient map with c = β(2) is injective. The coordinate along β(2) separates ℓ from ck.

**Theorem 1.4 (Evaluation on the first input block).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_K`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a finite extension E of a finite field F of order q, if K has degree three over F, then f(x) = ux + a₁x^q + a₂x^(q²) for every x in K and arbitrary b and c in E.

**Theorem 1.5 (Evaluation on the second input block).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_bK`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_bK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a finite extension E of a finite field F of order q, if K has degree three over F and δ is nonzero, then f(bx) = (ℓ + ck)x + a₁(bx)^q + a₂(bx)^(q²) for every x in K and arbitrary c in E.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.Params`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_K`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_bK`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients_injective`
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial](FerrersPolynomial.md)
