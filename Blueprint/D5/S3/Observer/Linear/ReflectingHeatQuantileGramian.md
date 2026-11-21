# Mode-uniform physical Gramian estimate

## Abstract

The quantile multiplier and the finite Blaschke estimate bound the inverse diagonal on each positive reflecting mode.

**Theorem 1.1 (Physical upper bound from the quantile multiplier).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.inverse_diagonal_upper_bound_of_quantiles`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.inverse_diagonal_upper_bound_of_quantiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-axis envelope cancels the exterior Joukowski radius in the Chebyshev interpolation bound. The imaginary-axis error bounds the multiplier value at the Fourier node −iq_j from below. Its radial exponential width gives the centered support, which becomes the physical interval of length a/n. The normalization retains the first-cell weight b_j and the nodal derivative combines with it to give q_j b_j.

**Theorem 1.2 (Finite Blaschke lower bound and angular quadrature).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.inverse_diagonal_lower_bound_at_saddle`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.inverse_diagonal_lower_bound_at_saddle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithm of the sum of two saddle radii increases along the angular grid. The right-endpoint sum bounds its angular average from above. Removing the endpoint at π and the selected positive mode costs at most twice the terminal logarithm. The resulting bound retains the exact factor q_j b_j and the time factor sqrt(na).

**Theorem 1.3 (Exact half-width of the saddle multiplier).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.canonicalProduct_type_at_saddle`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.canonicalProduct_type_at_saddle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Radial comparison gives a global exponential bound with coefficient na/2. Along the positive imaginary axis the evaluated potential has that linear term, and the angular average and first-bin discrepancy contribute only logarithmic terms. Dividing by the imaginary argument gives the limiting coefficient na/2.

**Theorem 1.4 (Uniform logarithmic loss at the continuum saddle).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.physical_log_inverse_diagonal_error`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.physical_log_inverse_diagonal_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the imaginary potential gives a weighted resolvent whose evaluation fixes the multiplier normalization. The identity theorem gives the potential on the right half-plane in the saddle square-root variable. Dominated convergence gives the real boundary value, including when the logarithm vanishes in its argument inside the support. The angular Green function equals the logarithm of the exterior Joukowski radius by the Mahler measure of a quadratic. Combining the resulting real-axis cancellation with the finite Blaschke lower bound gives an absolute logarithmic error at most 20(1+log n+|log(nT)|) on every positive mode.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.canonicalProduct_type_at_saddle`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.inverse_diagonal_lower_bound_at_saddle`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.inverse_diagonal_upper_bound_of_quantiles`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.physical_log_inverse_diagonal_error`
- Dependency: [D5/S3/Observer/Linear/ReflectingHeatPhysicalGramian](ReflectingHeatPhysicalGramian.md)
- Dependency: [D5/S3/Observer/Linear/ReflectingHeatSaddleBoundary](ReflectingHeatSaddleBoundary.md)
