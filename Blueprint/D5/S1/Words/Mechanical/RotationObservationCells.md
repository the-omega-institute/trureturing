# Rotation Observation Cells

## Abstract

Actual rotation readouts determine half-open phase cells, sharp phase decoders, and a unique new split.

**Definition 1.1 (Actual window observations).**

$$\forall alpha \in \mathbb{R},\; \forall n \in \mathbb{N},\; \forall x \in \mathbb{R},\; rotationPrefix\left(alpha, n, x\right) = k: Fin\left(n\right) \mapsto decide\left(1 - alpha \le fract\left(x + val\left(k\right) \cdot alpha\right)\right)$$

*Formalization.* `D5/S1/Words/Mechanical/RotationObservationCells.rotationPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binary word evaluates the indicator of [1-alpha,1) on the actual fractional iterates x+k*alpha. This is an observable on phases, rather than an abstract supplied partition.

**Theorem 1.2 (Exact fibers and all uniform decoders).**

$$\forall alpha \in \mathbb{R},\; \left(Irrational\left(alpha\right) \land \left(0 \le alpha \land alpha < 1\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \forall j \in Fin\left(n + 1\right),\; \{x \in \mathbb{R} \mid (x \in Ico\left(0, 1\right) \land rotationPrefix\left(alpha, n, x\right) = rotationPrefix\left(alpha, n, rotationCut\left(alpha, n + 1, castSucc\left(j\right)\right)\right))\} = Ico\left(rotationCut\left(alpha, n + 1, castSucc\left(j\right)\right), rotationCut\left(alpha, n + 1, succ\left(j\right)\right)\right) \land \left(\forall center \in \mathbb{R},\; \forall radius \in \mathbb{R},\; \left(\forall x \in \mathbb{R},\; x \in Ico\left(0, 1\right) \Rightarrow \left(rotationPrefix\left(alpha, n, x\right) = rotationPrefix\left(alpha, n, rotationCut\left(alpha, n + 1, castSucc\left(j\right)\right)\right) \Rightarrow \left|x - center\right| \le radius\right)\right) \Leftrightarrow \left(rotationCut\left(alpha, n + 1, succ\left(j\right)\right) - radius \le center \land center \le rotationCut\left(alpha, n + 1, castSucc\left(j\right)\right) + radius\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/RotationObservationCells.rotation_prefix_cell_and_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every irrational slope in [0,1), every prefix length and every sorted rotation arc, the actual observation fiber of its left endpoint is exactly that half-open arc. Every center and radius valid on the observed word is then characterized by b-radius <= center <= a+radius. The proof identifies bits with the existing mechanical word, reconstructs cumulative floors, proves equivalence with every rotation-cut test, and only then uses the sorted-arc owner. The radius lower bound handles the excluded right endpoint by an interior contradiction. No cylinder estimate or phase-decoding guarantee is a premise.

**Theorem 1.3 (A unique cell is split by the next observation).**

$$\forall alpha \in \mathbb{R},\; \left(Irrational\left(alpha\right) \land \left(0 \le alpha \land alpha < 1\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \left(\forall x \in \mathbb{R},\; x \in Ico\left(0, 1\right) \Rightarrow \left(\forall y \in \mathbb{R},\; y \in Ico\left(0, 1\right) \Rightarrow \left(rotationPrefix\left(alpha, n + 1, x\right) = rotationPrefix\left(alpha, n + 1, y\right) \Leftrightarrow \left(rotationPrefix\left(alpha, n, x\right) = rotationPrefix\left(alpha, n, y\right) \land \left(fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) \le x \Leftrightarrow fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) \le y\right)\right)\right)\right)\right) \land \left(\exists j \in Fin\left(n + 1\right),\; \left(rotationCut\left(alpha, n + 1, castSucc\left(j\right)\right) < fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) \land \left(fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) < rotationCut\left(alpha, n + 1, succ\left(j\right)\right) \land \left(\exists x \in \mathbb{R},\; \exists y \in \mathbb{R},\; x \in rotationGapArc\left(alpha, n + 1, j\right) \land \left(y \in rotationGapArc\left(alpha, n + 1, j\right) \land \left(x < fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) \land \left(fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) \le y \land \left(rotationPrefix\left(alpha, n, x\right) = rotationPrefix\left(alpha, n, y\right) \land \left(\neg rotationPrefix\left(alpha, n + 1, x\right) = rotationPrefix\left(alpha, n + 1, y\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\forall k \in Fin\left(n + 1\right),\; \left(rotationCut\left(alpha, n + 1, castSucc\left(k\right)\right) < fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) \land \left(fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) < rotationCut\left(alpha, n + 1, succ\left(k\right)\right) \land \left(\exists x \in \mathbb{R},\; \exists y \in \mathbb{R},\; x \in rotationGapArc\left(alpha, n + 1, k\right) \land \left(y \in rotationGapArc\left(alpha, n + 1, k\right) \land \left(x < fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) \land \left(fract\left(\left(n + 1\right) \cdot \left(-alpha\right)\right) \le y \land \left(rotationPrefix\left(alpha, n, x\right) = rotationPrefix\left(alpha, n, y\right) \land \left(\neg rotationPrefix\left(alpha, n + 1, x\right) = rotationPrefix\left(alpha, n + 1, y\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow k = j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/RotationObservationCells.rotation_prefix_single_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An additional actual bit adds exactly the threshold at fractional part -(n+1)*alpha to the old equality test. Irrationality proves this cut is absent from the old boundary set, so it lies strictly inside a unique old arc. Explicit phases on its two sides have equal old words and different extended words. Pairwise disjointness proves uniqueness; no list-refinement history is assumed. This establishes the geometric input needed for subsequent entropy and decision-risk consumers. Classical Sturmian complexity and the three-gap theorem are prior background, not claims of new discovery.

## References

- Truth anchor: `D5/S1/Words/Mechanical/RotationObservationCells.rotationPrefix`
- Truth anchor: `D5/S1/Words/Mechanical/RotationObservationCells.rotation_prefix_cell_and_decoder`
- Truth anchor: `D5/S1/Words/Mechanical/RotationObservationCells.rotation_prefix_single_cut`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](MechanicalBalance.md)
