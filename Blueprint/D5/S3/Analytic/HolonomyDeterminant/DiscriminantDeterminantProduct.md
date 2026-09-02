# Discriminant Determinant Product

## Abstract

The two mod-five sine determinants have golden ratio and discriminant product.

**Theorem 1.1 (The mod-five sector determinants recover the golden constants).**

$${2 \times \operatorname{sin}(\frac{\pi}{5})} \times {2 \times \operatorname{sin}(\frac{2 \times \pi}{5})} = \operatorname{sqrt}(5) \land \frac{2 \times \operatorname{sin}(\frac{2 \times \pi}{5})}{2 \times \operatorname{sin}(\frac{\pi}{5})} = goldenRatio$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/DiscriminantDeterminantProduct.discriminant_determinant_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two source sectors are represented by two times sine of pi over five and two times sine of two pi over five. Their product is the square root of five.

Ordering the second sector over the first gives the golden ratio. The proof uses the exact fifth-angle cosine value and the sine double-angle identity.

## References

- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/DiscriminantDeterminantProduct.discriminant_determinant_product`
