# The Shifted-Square Ascent Formula

## Abstract

A cyclicly shifted Latin square has an ascent total controlled by row ascents, endpoints, and unit cyclic steps.

**Definition 1.1 (Symbol transposition).**

$$\forall n \in \mathrm{Nat},\; \forall h \in \operatorname{Prop}\left(\right),\; \operatorname{swapFin}\left(n, h\right) = \operatorname{swap}\left(0, 1\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianFormula.swapFin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

For an order at least two, swapFin is the permutation exchanging the symbols zero and one.

**Definition 1.2 (Shifted Latin square).**

$$\forall n \in \mathrm{Nat},\; \forall h \in \operatorname{Prop}\left(\right),\; \forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall c \in \operatorname{Fin}\left(n\right),\; \operatorname{shiftedSquare}\left(n, h, p, i, c\right) = \operatorname{swapFin}\left(n, h, \operatorname{p}\left(i\right) + c\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianFormula.shiftedSquare` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The shifted square adds a column index to the row permutation and then applies the symbol transposition.

**Theorem 1.3 (Shifted pair count).**

$$\forall n \in \mathrm{Nat},\; \forall h \in \operatorname{Prop}\left(\right),\; \forall a \in \operatorname{Fin}\left(n\right),\; \forall b \in \operatorname{Fin}\left(n\right),\; \left(3 \le n \land \left(2 \le n \land a \ne b\right)\right) \Rightarrow \operatorname{card}\left(\{c \in \operatorname{Fin}\left(n\right)| \operatorname{swapFin}\left(n, h, a + c\right) < \operatorname{swapFin}\left(n, h, b + c\right)\}\right) + \operatorname{if}\left(\operatorname{val}\left(\operatorname{sub}\left(b, a\right)\right) = 1, 1, 0\right) = n - \operatorname{val}\left(\operatorname{sub}\left(b, a\right)\right) + \operatorname{if}\left(\operatorname{val}\left(\operatorname{sub}\left(b, a\right)\right) = n - 1, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinEulerianFormula.shifted_pair_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

For distinct row symbols, the swapped cyclic comparison count is n minus their cyclic difference, with the two endpoint corrections.

**Definition 1.4 (Cyclic row entry).**

$$\forall n \in \mathrm{Nat},\; \forall h \in \operatorname{Prop}\left(\right),\; \forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall j \in \mathrm{Nat},\; \operatorname{rowAt}\left(h, p, j\right) = \operatorname{p}\left(\operatorname{fin}\left(\operatorname{mod}\left(j, n\right), n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianFormula.rowAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

Read the permutation at a natural index reduced modulo the order.

**Definition 1.5 (Cyclic row difference).**

$$\forall n \in \mathrm{Nat},\; \forall h \in \operatorname{Prop}\left(\right),\; \forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall j \in \mathrm{Nat},\; \operatorname{rowDelta}\left(h, p, j\right) = \operatorname{rowAt}\left(h, p, j + 1\right) - \operatorname{rowAt}\left(h, p, j\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianFormula.rowDelta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The cyclic difference is the next row entry minus the current row entry in Fin n.

**Definition 1.6 (Ordinary row ascents).**

$$\forall n \in \mathrm{Nat},\; \forall h \in \operatorname{Prop}\left(\right),\; \forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{ordinaryAscents}\left(h, p\right) = \sum j \in \operatorname{range}\left(n - 1\right) \operatorname{if}\left(\operatorname{rowAt}\left(h, p, j\right) < \operatorname{rowAt}\left(h, p, j + 1\right), 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianFormula.ordinaryAscents` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

Count increasing adjacent entries of the row permutation over the noncyclic indices.

**Definition 1.7 (Forward unit steps).**

$$\forall n \in \mathrm{Nat},\; \forall h \in \operatorname{Prop}\left(\right),\; \forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{forwardUnits}\left(h, p\right) = \sum j \in \operatorname{range}\left(n - 1\right) \operatorname{if}\left(\operatorname{val}\left(\operatorname{rowDelta}\left(h, p, j\right)\right) = 1, 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianFormula.forwardUnits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

Count cyclic differences whose Fin representative is one.

**Definition 1.8 (Backward unit steps).**

$$\forall n \in \mathrm{Nat},\; \forall h \in \operatorname{Prop}\left(\right),\; \forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{backwardUnits}\left(h, p\right) = \sum j \in \operatorname{range}\left(n - 1\right) \operatorname{if}\left(\operatorname{val}\left(\operatorname{rowDelta}\left(h, p, j\right)\right) = n - 1, 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianFormula.backwardUnits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

Count cyclic differences whose Fin representative is n minus one.

**Theorem 1.9 (Shifted-square ascent identity).**

$$\forall n \in \mathrm{Nat},\; \forall h \in \operatorname{Prop}\left(\right),\; \forall hp \in \operatorname{Prop}\left(\right),\; \forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \left(3 \le n \land \left(2 \le n \land 0 < n\right)\right) \Rightarrow \operatorname{Int}\left(\operatorname{totalAscents}\left(n, \operatorname{shiftedSquare}\left(n, h, p\right)\right)\right) = n \cdot \operatorname{ordinaryAscents}\left(hp, p\right) + \operatorname{val}\left(\operatorname{rowAt}\left(hp, p, 0\right)\right) - \operatorname{val}\left(\operatorname{rowAt}\left(hp, p, n - 1\right)\right) - \operatorname{forwardUnits}\left(hp, p\right) + \operatorname{backwardUnits}\left(hp, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinEulerianFormula.shiftedSquare_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The total ascent count equals n times the ordinary row ascents, plus the endpoint difference, minus forward unit steps, plus backward unit steps.

## References

- Truth anchor: `D5/S3/Combinatorics/LatinEulerianFormula.backwardUnits`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianFormula.forwardUnits`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianFormula.ordinaryAscents`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianFormula.rowAt`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianFormula.rowDelta`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianFormula.shiftedSquare`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianFormula.shiftedSquare_formula`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianFormula.shifted_pair_count`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianFormula.swapFin`
- Dependency: [D5/S3/Combinatorics/LatinEulerianCounting](LatinEulerianCounting.md)
- Dependency: [D5/S3/Combinatorics/LatinEulerianShiftCount](LatinEulerianShiftCount.md)
