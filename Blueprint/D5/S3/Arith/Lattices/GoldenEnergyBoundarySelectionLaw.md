# Golden Energy-Boundary Selection Law

## Abstract

Golden prime classes and the unique ramified modulus govern the lattice energy boundary.

**Theorem 1.1 (Golden prime behavior selects the mod-five energy boundary).**

$$\begin{aligned}\forall x: \operatorname{Fin}(6) \to \mathbb{Z}, \operatorname{boundaryQuadratic}(\operatorname{boundaryProjection}(x)) = 2\cdot \operatorname{latticeEnergyModFive}(x) \land\\{}\forall x, y: \operatorname{Fin}(6) \to \mathbb{Z}, \operatorname{latticeEnergyModFive}(x) = \operatorname{latticeEnergyModFive}(y) \Rightarrow \operatorname{boundaryQuadratic}(\operatorname{boundaryProjection}(x)) = \operatorname{boundaryQuadratic}(\operatorname{boundaryProjection}(y)) \land\\{}\forall p \in \mathbb{N}, \operatorname{Prime}(p) \Rightarrow (((\operatorname{mod}(p, 5) = 1 \lor \operatorname{mod}(p, 5) = 4) \Rightarrow \neg\operatorname{Prime}(\operatorname{cast}(p, GoldenInt))) \land ((\operatorname{mod}(p, 5) = 2 \lor \operatorname{mod}(p, 5) = 3) \Rightarrow \operatorname{Prime}(\operatorname{cast}(p, GoldenInt)))) \land\\{}(\operatorname{cast}(5, GoldenInt) = (-1 + 2\varphi)^{2} \land \neg\operatorname{Prime}(\operatorname{cast}(5, GoldenInt))) \land\\{}\forall p \in \mathbb{N}, \operatorname{Prime}(p) \Rightarrow (\operatorname{legendreSym}(5, p) = 0 \Leftrightarrow p = 5).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/GoldenEnergyBoundarySelectionLaw.golden_energy_boundary_selection_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integral vector in the canonical six-coordinate lattice obeys the energy-boundary equality. Equality of two energy residues therefore forces equality of their boundary quadratic types.

For every rational prime, residues one and four modulo five give a split image in the golden integers, while residues two and three give an inert image. These are the plus-or-minus one and plus-or-minus two classes, respectively.

Five is the square of the ramifying golden integer and is not prime in the golden integer ring. The quadratic character modulo five vanishes at no other rational prime, exposing the unique finite ramified location used by the lattice boundary.

The proof imports the frozen energy, golden-prime classification, and ramified-boundary owners. Pinned Mathlib has the Legendre zero and prime-divisibility facts used by those owners, but no exact theorem combining all five public clauses.

## References

- Truth anchor: `D5/S3/Arith/Lattices/GoldenEnergyBoundarySelectionLaw.golden_energy_boundary_selection_law`
- Dependency: [D5/S3/Arith/Lattices/RamifiedFiveBoundarySelection](RamifiedFiveBoundarySelection.md)
