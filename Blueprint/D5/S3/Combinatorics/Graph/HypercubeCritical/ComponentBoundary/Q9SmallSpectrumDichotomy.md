# Component orders under the paired-fibre alternative

## Abstract

Component orders under the paired-fibre alternative

**Theorem 1.1 (Order 72 forces one projected parity on every axis).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy.pure_parity_of_order_seventy_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy.pure_parity_of_order_seventy_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A full eight-star supplies pairs in both parities along each other axis. At order 72 this would force all axes to carry full stars, contradicting the packing bound.

**Theorem 1.2 (The order-84 split violates parity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy.order_ne_eighty_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy.order_ne_eighty_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divisibility forces a thirteen-to-one split wherever one parity contains twelve or more double fibres. Star packing and the minority counts force the split on all nine axes, contradicting the descending-edge congruence.

**Theorem 1.3 (The first remaining order is at least 90).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy.ninety_le_of_not_seventy_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy.ninety_le_of_not_seventy_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given the local eight-star or twelve-pair alternative on every axis and exclusion of the adjacent-layer order-72 case, the projected parity counts and the congruence exclude the intervening orders. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy.ninety_le_of_not_seventy_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy.order_ne_eighty_four`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy.pure_parity_of_order_seventy_two`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity](Q9DescendingEdgeParity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking](Q9EightStarFootprintPacking.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers](Q9PureParityLayers.md)
