# The Three-Row Blackout Maximum

## Abstract

A three-row lattice grid of every width at least three admits exactly the conjectured maximum number of blacked-out points.

**Definition 1.1 (The full rectangle family).**

$$\forall m:\mathbb{N}, \forall C:\operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(3\right)\right), \operatorname{IsRectangle}\left(C\right)\iff\left(\operatorname{card}\left(C\right)=4\land\exists a b c d:\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(3\right), C=\{a,b,c,d\}\land\left(\operatorname{x}\left(b\right)-\operatorname{x}\left(a\right)\right)\cdot\left(\operatorname{x}\left(c\right)-\operatorname{x}\left(a\right)\right)+\left(\operatorname{y}\left(b\right)-\operatorname{y}\left(a\right)\right)\cdot\left(\operatorname{y}\left(c\right)-\operatorname{y}\left(a\right)\right)=0\land\operatorname{x}\left(a\right)+\operatorname{x}\left(d\right)=\operatorname{x}\left(b\right)+\operatorname{x}\left(c\right)\land\operatorname{y}\left(a\right)+\operatorname{y}\left(d\right)=\operatorname{y}\left(b\right)+\operatorname{y}\left(c\right)\right)$$

*Formalization.* `D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum.IsRectangle` (`✓ std3`).

*Citation.* Arjun Pemmasani (2026). *Blackouts Preserving Rectangle Identifiability on Grid Points: A partial solution to Problem 001 of Kagey's Open Problem Collection*. URL: <https://github.com/apemm/Kagey-Problems/blob/b9567e4dc1c7cf1e5034569571a9479b1b83dc57/kagey-problems/problem001/paper/main.tex>.

*Commentary.*

The first coordinate is column and the second row. In this formula x and y are the respective coordinate values cast to integers. Four distinct corners, perpendicular adjacent vectors and the parallelogram equations describe every nondegenerate Euclidean rectangle on the grid, including squares and tilted rectangles. Corner sets are unordered.

**Definition 1.2 (Identifiability after deletion).**

$$\forall m:\mathbb{N}, \forall S:\operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(3\right)\right), \operatorname{ValidBlackout}\left(S\right)\iff\left(\forall C D:\operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(3\right)\right), \operatorname{IsRectangle}\left(C\right)\implies \operatorname{IsRectangle}\left(D\right)\implies C\setminus S=D\setminus S\implies C=D\right)$$

*Formalization.* `D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum.ValidBlackout` (`✓ std3`).

*Citation.* Arjun Pemmasani (2026). *Blackouts Preserving Rectangle Identifiability on Grid Points: A partial solution to Problem 001 of Kagey's Open Problem Collection*. URL: <https://github.com/apemm/Kagey-Problems/blob/b9567e4dc1c7cf1e5034569571a9479b1b83dc57/kagey-problems/problem001/paper/main.tex>.

*Commentary.*

A blackout is chosen before the rectangle. Its presentation is the corner set after deleting blacked-out points. Validity requires that equal presentations imply equal corner sets. Empty presentations are allowed; injectivity itself ensures that at most one rectangle is entirely hidden.

**Theorem 1.3 (Pemmasani's exact maximum).**

$$\forall m:\mathbb{N}, 3\leq m\implies \left(\exists S:\operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(3\right)\right), \operatorname{ValidBlackout}\left(S\right)\land\operatorname{card}\left(S\right)=m+2\right)\land\left(\forall S:\operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(3\right)\right), \operatorname{ValidBlackout}\left(S\right)\implies \operatorname{card}\left(S\right)\leq m+2\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397315-three-row-blackout` (proved) by `D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397315-three-row-blackout","declaration_gid":"D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arjun Pemmasani (2026). *Blackouts Preserving Rectangle Identifiability on Grid Points: A partial solution to Problem 001 of Kagey's Open Problem Collection*. URL: <https://github.com/apemm/Kagey-Problems/blob/b9567e4dc1c7cf1e5034569571a9479b1b83dc57/kagey-problems/problem001/paper/main.tex>.

*Acknowledgement.* Hector J. Partridge (2017). *OEIS A289832, rectangles in rectangular lattice grids*. URL: <https://oeis.org/A289832>.

*Commentary.*

For every natural width at least three, the theorem constructs a valid blackout with width plus two points and proves that every valid blackout has at most that size. Both clauses refer to the full rectangle family.

The attaining set is the union of a boundary row and a boundary column. The proof establishes the known classification from Partridge's A289832: all three-row rectangles are axis rectangles or unit diamonds on three consecutive columns. Their visible corners distinguish all pairs after this deletion.

For the upper bound, two different columns cannot both hide the same pair of rows: comparison with a third column would give colliding rectangle presentations. This is Pemmasani's two-row Strip Theorem obstruction, proved locally. A second collision rules out independent overlaps of all three row pairs. Finite-set inclusion-exclusion then bounds the total by the width plus two. No source numerical table or diagram is used as a premise.

## References

- Truth anchor: `D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum.IsRectangle`
- Truth anchor: `D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum.ValidBlackout`
- Truth anchor: `D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum.result`
