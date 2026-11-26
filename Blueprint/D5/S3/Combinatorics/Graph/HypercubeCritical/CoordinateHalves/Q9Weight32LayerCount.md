# At most eight axial layer settings survive up to layer swap

## Abstract

Signed square cancellation bounds the number of binary axial completions.

**Theorem 1.1 (Degree-two rows determine distinct pairs of support sites).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32LayerCount.degreeTwoRows_injOn_neighborPair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32LayerCount.degreeTwoRows_injOn_neighborPair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the signed support word have values ±1 on its support and zero elsewhere, with every Huang row divisible by four. Two distinct rows with the same neighbor pair would meet that pair in one square. The products of Huang signs around the square force the signed sums at the two rows to have different magnitudes, contradicting the signed row equation.

**Theorem 1.2 (At most eight axial layer settings survive up to layer swap).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32LayerCount.card_axialLayerSettings_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32LayerCount.card_axialLayerSettings_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a signed word v of weight 32 with values ±1 on its support and zero elsewhere. Suppose every unsigned row degree is zero, two, or four and the signed equation is Av = −4e over the integers. The binary row target is the support indicator of e. The result bounds its fiber by sixteen settings and eight classes under complementation. Every nonconstant word in the binary neighbor kernel has weight sixteen. All coordinate evaluation classes therefore have equal size. At least eighteen degree-two rows give distinct pairs on thirty-two sites. Two pairs share a site, so its evaluation class contains at least three coordinates. The product of the class size and kernel size is sixty-four, ruling out class size three. The kernel has at most sixteen elements. The all-one word exchanges the layer bits. Each class has a unique representative that sets one fixed support bit to zero. The signed reconstruction from the binary completion criterion applies this count to a 72-vertex component case in the repository’s reduction of the size-258 question. See Hong–Wu–Xia, Section 7, Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32LayerCount.card_axialLayerSettings_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32LayerCount.degreeTwoRows_injOn_neighborPair`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnIntegrality](../ComponentBoundary/HuangThreeColumnIntegrality.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCodeCoordinateClass](BinaryCodeCoordinateClass.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion](Q9BinaryAxialCompletion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows](Q9Weight32DegreeTwoRows.md)
