# Weighted occupation pairs with disjoint supports

## Abstract

Disjoint supports give a product bound for two multinomial count vectors.

**Theorem 1.1 (Exponential bound for disjoint occupation mass).**

$$s^{2d}U_{d} \leq B \leq (d!)^{2}e^{2sW - \sum_{j}(1-e^{-sw_{j}})^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DisjointSupportOccupationMass.scaled_disjoint_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a finite index set with nonnegative weights w. For a nonnegative integer d, U with subscript d sums the products of the weighted multinomial coefficients of two degree-d vectors with disjoint supports. Write W for the total weight and take s≥0. Let B be the square of d factorial times the product over j of 2 exp(s w(j)) minus one.

After scaling by the power of s and extracting the two factorials, each coordinate contributes (s w(j))^(a+b)/(a! b!). The map taking an occupation pair to its coordinate pairs is injective and lands in the product of the finite sets with 0≤a,b≤d and a=0 or b=0. Since all terms are nonnegative, dropping both total-degree constraints increases the sum. The local sum consists of two exponential partial sums with the common zero pair counted once.

The local factor at x=s w(j) is exp(2x) times 1−(1−exp(−x))². Bounding each latter factor by the exponential with the same quadratic penalty gives the second inequality. The same bound applies if a frequency-resolution condition further restricts the disjoint occupation pairs.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/DisjointSupportOccupationMass.scaled_disjoint_mass`
- Dependency: [D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow](FiniteTailMomentMissingWindow.md)
