# Layers of the Golden Heat Spectrum

## Abstract

The golden heat spectrum splits into prime layers whose convergence abscissae strictly decrease to zero, so the abscissa of the whole trace is set by the ground layer alone.

**Theorem 1.1 (The golden Euler exponents are strictly increasing).**

$$\forall u, v \in \mathbb{N}, u < v \implies \operatorname{o5Beta}(u) < \operatorname{o5Beta}(v).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatLayers/GoldenHeatLayers.o5_beta_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed form of the exponent account separates a linear term from a fractional part, and the linear increment exceeds the largest possible swing of that fractional part; strict monotonicity follows on consecutive indices.

**Theorem 1.2 (Each golden layer has a boundary-divergent abscissa).**

$$\forall k \in \mathbb{N}, \operatorname{BoundaryDivergentAbscissa}(\operatorname{goldenLayer}(k), \frac{1}{\operatorname{o5Beta}(k+1)}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_layer_boundary_divergent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every layer index the prime series converges strictly to the right of the reciprocal exponent, diverges strictly to its left, and diverges on the boundary itself, where the layer reduces to the reciprocals of the primes.

**Theorem 1.3 (The layer abscissae strictly decrease).**

$$\forall j, k \in \mathbb{N}, j < k \implies \frac{1}{\operatorname{o5Beta}(k+1)} < \frac{1}{\operatorname{o5Beta}(j+1)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_layer_abscissa_strictAnti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict monotonicity of the exponents inverts to strict antitonicity of their reciprocals, so a higher layer always converges strictly further to the left.

**Theorem 1.4 (The layer abscissae tend to zero).**

$$\operatorname{Tendsto}(k \mapsto \frac{1}{\operatorname{o5Beta}(k+1)}, \operatorname{atTop}, \operatorname{nhds}(0)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_layer_abscissa_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linear lower bound on the exponent account drives the exponents to infinity along the layer index, so their reciprocals converge to zero; no layer abscissa is ever attained at zero.

**Theorem 1.5 (Every excited layer lies strictly left of the ground abscissa).**

$$\forall k \in \mathbb{N}, 0 < k \implies \frac{1}{\operatorname{o5Beta}(k+1)} < \frac{1}{\varphi^{2}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_excited_layer_abscissa_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ground layer carries the abscissa one over phi squared, and every excited layer sits strictly to its left. The abscissa of the full two-parameter trace is therefore fixed by the ground layer alone: every excited layer still converges at that threshold, so the divergence pinning the trace's abscissa is witnessed by the ground layer by itself.

## References

- Truth anchor: `D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_excited_layer_abscissa_lt`
- Truth anchor: `D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_layer_abscissa_strictAnti`
- Truth anchor: `D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_layer_abscissa_tendsto_zero`
- Truth anchor: `D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_layer_boundary_divergent`
- Truth anchor: `D5/S3/Midline/HeatLayers/GoldenHeatLayers.o5_beta_strictMono`
- Dependency: [D5/S3/Midline/GoldenHeatSpectrum](../GoldenHeatSpectrum.md)
- Dependency: [D5/S3/Midline/UniversalHeatTrace](../UniversalHeatTrace.md)
