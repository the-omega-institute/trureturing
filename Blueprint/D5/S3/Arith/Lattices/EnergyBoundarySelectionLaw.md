# Energy-Boundary Selection Law

## Abstract

The explicit five-adic boundary map carries lattice energy to twice its residue.

**Theorem 1.1 (Boundary type is selected by lattice energy modulo five).**

$$\forall x: \mathbb{Z}^{6}, \operatorname{boundaryQuadratic}\left(\operatorname{boundaryProjection}\left(x\right)\right) = 2\cdot \operatorname{latticeEnergyModFive}\left(x\right), \operatorname{in} \operatorname{ZMod}\left(5\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/EnergyBoundarySelectionLaw.energy_boundary_selection_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral carrier is the lattice Lambda^2 A4 in its chosen six-vector basis. The imported integralGramMatrix is the source's displayed six-by-six Gram matrix, so every integral coordinate vector is an element of that lattice rather than a surrogate finite carrier.

The boundaryProjectionMatrix is the displayed three-by-six matrix over ZMod 5, and boundaryProjection first reduces the integral coordinates modulo five before multiplying by that matrix. The boundary quadratic form uses the displayed symmetric three-by-three matrix.

Expanding both matrix products proves the nontrivial polynomial identity for all six integral coordinates. Thus the boundary quadratic value equals twice the Gram energy in ZMod 5.

## References

- Truth anchor: `D5/S3/Arith/Lattices/EnergyBoundarySelectionLaw.energy_boundary_selection_law`
- Dependency: [D5/S3/Arith/Lattices/ExactDualLatticeFormula](ExactDualLatticeFormula.md)
