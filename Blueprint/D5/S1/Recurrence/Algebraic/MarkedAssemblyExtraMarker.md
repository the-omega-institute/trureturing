# Local coefficient integrality with an extra root marker

## Abstract

One extra ambient marker on the pointed assembly increases the coefficient multiplier by one power.

**Theorem 1.1 (The mixed-power strict-prefix residual).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall a: \operatorname{Function}\left(\mathbb{N}, \mathbb{Z}\right), \forall p: \mathbb{N}, (1 \le N \land \left(\operatorname{Prime}\left(p\right) \land \left(\neg \operatorname{Dvd}\left(p, N\right) \land \forall f: \mathbb{N}, (1 \le f) \implies ((f < N) \implies (\operatorname{coeff}\left(f, \operatorname{exp}\left((\operatorname{castQ}\left(f\right))^{d} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right) = (\operatorname{castQ}\left(f\right))^{d + 1} \cdot \operatorname{coeff}\left(f - 1, \operatorname{exp}\left((\operatorname{castQ}\left(f\right))^{d} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right)))\right)\right)) \implies (0 \le \operatorname{padicValRat}\left(p, \operatorname{coeff}\left(N, \operatorname{exp}\left((\operatorname{castQ}\left(N\right))^{d} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right) - (\operatorname{castQ}\left(N\right))^{d + 1} \cdot \operatorname{coeff}\left(N - 1, \operatorname{exp}\left((\operatorname{castQ}\left(N\right))^{d} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MarkedAssemblyExtraMarker.signed_prefix_residual_local_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict prefix P has ordinary coefficient a(j) for 0<j<N and zero otherwise. Every block has d ambient markers. The pointed object with one more marker is the product of the usual pointed assembly with the ambient vertex type, with the diagonal permutation action. Its weight is inherited from the assembly. A permutation with f fixed vertices multiplies the original pointed fixed-point sum by f. Subtracting the new pointed sum from the full sum gives the lower residual with exponential scalar f to the power d and multiplier f to the power d+1, times f! and the common moved-block weight sum. Each nonidentity Sylow element has between one and N-1 fixed vertices, so its residual vanishes by the lower equations. At the identity, the moved-block sum is one. Signed Burnside gives divisibility of the identity subtraction by the full Sylow order, cancelling the entire p-adic valuation of N!.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MarkedAssemblyExtraMarker.signed_prefix_residual_local_integral`
- Dependency: [D5/S1/Recurrence/Algebraic/MarkedAssemblyCoefficients](MarkedAssemblyCoefficients.md)
