# Binary vertex colors and flat-angle patterns

## Abstract

Balanced binary vertex colorings classify the three opposite-edge flat-angle patterns.

Color the four vertices with two symbols, with exactly two vertices of each color. Boolean XOR represents addition in the two-element field. The three standard colorings are (0,0,1,1), (0,1,0,1), and (0,1,1,0); their equal-color edges are respectively the opposite pairs 12 and 34, 13 and 24, and 14 and 23.

**Theorem 1.1 (Three flat-angle states from balanced vertex colors).**

$$\left(\forall k \in Fin\left(3\right),\; balanced\left(stateColor\left(k\right)\right) = true \land corresponds\left(stateColor\left(k\right), k\right) = true\right) \land \left(\left(\forall b \in Fin\left(4\right) \to Bool,\; balanced\left(b\right) = true \Rightarrow length\left(filter\left(finRange\left(3\right), k \mapsto corresponds\left(b, k\right)\right)\right) = 1\right) \land \left(\forall b \in Fin\left(4\right) \to Bool, i \in Fin\left(4\right), j \in Fin\left(4\right),\; flatAngle\left(b, i, j\right) = \pi\cdot {1-toNat\left(crossing\left(b, i, j\right)\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/VertexStateColoring.balanced_coloring_flat_angle_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each standard coloring has two vertices of each color and matches its stated opposite-edge pair. Every balanced coloring matches exactly one of these three edge patterns. Swapping both vertex colors preserves the pattern, so the patterns classify the unlabelled two-two partitions.

An edge joining equal colors receives flat extension angle pi; an edge joining different colors receives zero. The XOR crossing bit is one exactly on the latter edges, giving the angle as pi times one minus that bit.

This is a local classification of angle patterns. It supplies neither a positive length realizing a flat block nor a compatible coloring of globally identified vertices.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/VertexStateColoring.balanced_coloring_flat_angle_correspondence`
