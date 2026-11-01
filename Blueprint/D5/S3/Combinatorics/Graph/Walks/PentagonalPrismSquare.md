# The square of the pentagonal prism

## Abstract

Explicit Chinese-remainder coordinates identify the square complement with a ten-cycle.

P5 is the native Cartesian graph cycleGraph(5) box-product K2. Map a ten-cycle vertex j to (2j mod 5,j mod 2). The Chinese remainder equivalence, followed by multiplication by the unit 2 modulo 5, supplies a bijection of the actual vertices. The cycle and product distance suppliers check adjacency in both directions.

**Definition 1.1 (The actual complement-cycle correspondence).**

$$\operatorname{GraphIso}\left(\operatorname{cycleGraph}\left(10\right), \operatorname{complement}\left(\operatorname{power}\left(\operatorname{prism}\left(2\right), 2\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/PentagonalPrismSquare.pentagon_square_complement_iso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two prism vertices fail to be adjacent in its square exactly when their base cycle separation is two and their binary labels differ. Under the displayed coordinates these are precisely consecutive vertices of the ten-cycle. A triangle-free graph without isolated vertices has two-vertex maximal cliques, so the general complement-spectrum supplier proves the middle power directly in the all-positive-power classification. Pham and Vu, arXiv 2610.09300v1 Example 3.8, already give this well-covered-powers example; no novelty is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/PentagonalPrismSquare.pentagon_square_complement_iso`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum](BinaryRungSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure](PowerSpectrumStructure.md)
