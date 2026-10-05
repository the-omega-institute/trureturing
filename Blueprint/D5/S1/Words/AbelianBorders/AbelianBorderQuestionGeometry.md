# The Geometry of the Ternary Path

## Abstract

The continuous ternary path stays in a rational-axis cylinder and revisits every tangential line with bounded gaps.

**Definition 1.1 (The diagonal axis).**

$$axis = (1, 1, 1)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionGeometry.axis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The axis direction is (1,1,1), a nonzero vector with rational coordinates.

**Definition 1.2 (Four vertices modulo the axis).**

$$map\left(vertex, [0, 1, 2, 3]\right) = [(-3, -3, 0), (0, -3, 0), (2, 2, 0), (0, 2, 0)]$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionGeometry.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The representatives are (-3,-3,0), (0,-3,0), (2,2,0), and (0,2,0). Projection by T(p)=(p0-p2,p1-p2) sends them to the four vertices of a quadrilateral containing the projected path.

**Theorem 1.3 (Cylinder containment and recurrent tangential lines).**

$$GeometricHypotheses\left(word\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AbelianBorders/AbelianBorderQuestionGeometry.geometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

Every point of the continuous graph is a convex combination of the four representatives plus a real multiple of the diagonal axis. The four exposed vertex lines each contain a cut point in every window from n through n+60. A supporting hyperplane whose contacts lie on a single axis-parallel line forces that line to be one of these exposed vertex lines. Thus cylinder containment and the required bounded tangential gaps both hold.

## References

- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionGeometry.axis`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionGeometry.geometric`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionGeometry.vertex`
- Dependency: [D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord](AbelianBorderQuestionWord.md)
