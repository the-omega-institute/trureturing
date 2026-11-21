# Canonical quantile product

## Abstract

The canonical heat multiplier is the product over the positive equal-mass right endpoints.

**Theorem 1.1 (Entire canonical multiplier).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bound on the density forces the positive endpoints to grow at least linearly in their index. Their inverse squares are summable. This gives locally uniform convergence of the paired-zero factors, so the limit is entire.

**Theorem 1.2 (Real-axis estimate with logarithmic clipping).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_real_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_real_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The clipped logarithm decreases to its minimum and then increases to zero. Its signed quadrature error costs at most log(1+|x|/δ). The integral of the clipping correction with density bounded by D costs at most 2Dδ. Choosing δ=1/D yields the factor exp(2)(1+D|x|). The finite-product comparison includes zeros of the product.

**Theorem 1.3 (Signed imaginary-axis estimate).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_imaginary_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_imaginary_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At either imaginary argument the factors are positive. The decreasing kernel log(1+y²/t²) identifies the signed logarithmic discrepancy, with a cost of at most log(1+y²/β²) in the lower bound.

**Theorem 1.4 (Radial half-width bound).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_half_width`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_half_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each factor on a circle is bounded in modulus by its value on the imaginary axis. The signed imaginary-axis upper estimate transfers a bound of Ly/2 for the potential to a radial exponential bound of half-width L/2.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_entire`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_half_width`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_imaginary_bounds`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_real_bound`
- Dependency: [D5/S3/Observer/Linear/ReflectingHeatQuantile](ReflectingHeatQuantile.md)
