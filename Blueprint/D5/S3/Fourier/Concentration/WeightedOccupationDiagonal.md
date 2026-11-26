# The weighted occupation diagonal

## Abstract

A positive coefficient comparison bounds the diagonal of a weighted multinomial moment.

**Theorem 1.1 (Product bound for the scaled diagonal).**

$$0 \leq s \implies s^{p} D_{p}(w) \leq (p!)^{2} \prod_{j \in J} A(s \left(w_{j}\right)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/WeightedOccupationDiagonal.scaled_diagonal_le_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be finite, w be real weights on J, p be a nonnegative integer, and s be a nonnegative real number. The diagonal D with subscript p sums the squares of the weighted multinomial coefficients of degree p. The envelope A(x) is 2 exp(x/2) minus one.

Multiply the diagonal by s to the power p and divide by the square of p factorial. The resulting terms are coordinate products of (s w(j)²)^n/(n!)². Extending the sum to all vectors with coordinates between zero and p gives a product of nonnegative partial sums.

For n≥1 the bound n!≥2^(n−1) follows by induction. Each positive-degree term is thus bounded by twice the corresponding exponential term at half the argument. The constant coefficient is one, so the coordinate partial sum is at most A(x). The product preserves these separate coordinate bounds.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/WeightedOccupationDiagonal.scaled_diagonal_le_product`
- Dependency: [D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow](FiniteTailMomentMissingWindow.md)
