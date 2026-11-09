# Sparse cusp transport

## Abstract

Transport of sparse cusp energy to the original price-weighted response.

**Definition 1.1 (Price-weighted profile cross energy).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The profile cross energy integrates the product of the actual constant-profile responses at exponents a and b against dx/x over [X,2X].

**Theorem 1.2 (Normalized response of an isolated spike).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileResponse_spike_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileResponse_spike_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an admissible spike and every x between its center X and 2X, with 0 <= theta <= b <= 1, the response divided by sqrt(x) equals A/x^theta times the unit integral of the cusp increment multiplied by the original price ratio. Isolation holds for every forward displacement up to 2X^b.

**Theorem 1.3 (Integrability of mixed responses).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two locally bounded measurable error functions and arbitrary exponents, the product of their constant-profile responses divided by x is integrable on each compact interval above three.

**Theorem 1.4 (Price removal for a sparse cusp).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_spike_price_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_spike_price_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If X is an admissible spike center above four and 8X^b/X <= 1, the difference between its actual cross energy and A^2 times the moving cusp energy has absolute value at most 16X^b/X times that unweighted moving energy. Both price ratios are nonnegative.

**Theorem 1.5 (Transported cusp energy estimate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_spike_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_spike_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<a<b<1 and an admissible starting index, there is C>0 such that eventually at the centers X, writing h=X^a, k=X^b and L=log(k/h), the actual cross energy differs from A^2 X^(-a-b) hL^2/4 by at most C A^2 X^(-a-b) times hL+(k/X)hL^2.

**Theorem 1.6 (Cross energy at the spike centers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_spike_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_spike_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<a<b<1 and an admissible starting index, the actual constant-profile cross energy divided by X^(1-b)log(X)^3/log(log(X)) tends along the spike centers to (b-a)^2/4. The product normalization is exactly x^(-a-b).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_spike_asymptotic`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_spike_estimate`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileCross_spike_price_error`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.profileResponse_spike_normalized`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CuspMovingLengths](CuspMovingLengths.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes](SparseLogSpikes.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightRemoval](WeightRemoval.md)
